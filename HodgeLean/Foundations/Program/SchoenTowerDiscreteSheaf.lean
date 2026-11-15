import HodgeLean.Foundations.Program.SchoenExceptionalProperExact

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace HodgeLean.Foundations.Program

theorem s2v_discreteSheaf_extend {T : TopCat.{0}} [DiscreteTopology T]
    (F : TopCat.Sheaf AddCommGrpCat.{0} T) (U : Opens T) (s : F.obj.obj (op U)) :
    ∃ t : F.obj.obj (op ⊤), F.obj.map (homOfLE le_top : U ⟶ ⊤).op t = s := by
  let C : Opens T := ⟨(U : Set T)ᶜ, isOpen_discrete _⟩
  have hsup : U ⊔ C = ⊤ := by ext x; simp [C]
  have hbot : U ⊓ C = ⊥ := by ext x; simp [C]
  have hc : F.obj.map (homOfLE (inf_le_left : U ⊓ C ≤ U)).op s =
      F.obj.map (homOfLE (inf_le_right : U ⊓ C ≤ C)).op 0 := by
    apply F.eq_of_locally_eq' (fun _ : Fin 0 => (⊥ : Opens T)) (U ⊓ C)
      (fun i => Fin.elim0 i) (by simp [hbot])
    intro i
    exact Fin.elim0 i
  obtain ⟨t, ht, -⟩ := s3_soft_glue₂ F s 0 hc
  refine ⟨F.obj.map (eqToHom hsup.symm).op t, ?_⟩
  rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp]
  have hm : (eqToHom hsup.symm).op ≫ (homOfLE le_top : U ⟶ ⊤).op =
      (homOfLE (le_sup_left : U ≤ U ⊔ C)).op := Subsingleton.elim _ _
  rw [hm]
  exact ht

theorem s2v_discreteSheaf_isFlasque {T : TopCat.{0}} [DiscreteTopology T]
    (F : TopCat.Sheaf AddCommGrpCat.{0} T) : F.IsFlasque := by
  constructor
  intro U V i
  apply (AddCommGrpCat.epi_iff_surjective _).mpr
  intro s
  obtain ⟨t, ht⟩ := s2v_discreteSheaf_extend F V.unop s
  refine ⟨F.obj.map (homOfLE le_top : U.unop ⟶ ⊤).op t, ?_⟩
  rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp]
  exact ht

theorem s2v_discreteSheaf_cohomology_succ {T : TopCat.{0}}
    [DiscreteTopology T] [CompactSpace T] [T2Space T]
    (F : TopCat.Sheaf AddCommGrpCat.{0} T) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H F (n + 1)) := by
  letI := s2v_discreteSheaf_isFlasque F
  exact s3_subsingleton_cohomology_succ_of_isSoft F (s3_isSoft_of_isFlasque F) n

theorem s2v_proper_finiteFibres_pushforward_shortExact {X Y : TopCat.{0}}
    [T2Space X] [LocallyCompactSpace X] (p : X ⟶ Y) (hp : IsProperMap p)
    (hfin : ∀ y : Y, Set.Finite {x : X | p x = y})
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)} (hS : S.ShortExact) :
    (S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{0} p)).ShortExact := by
  apply s3_proper_pushforward_shortExact p hp hS
  intro y
  letI : Finite {x : X // p x = y} := (hfin y).to_subtype
  letI : DiscreteTopology {x : X // p x = y} :=
    @Finite.instDiscreteTopology _ _ inferInstance (hfin y).to_subtype
  letI : CompactSpace {x : X // p x = y} := s3_fibre_compactSpace p hp y
  exact s2v_discreteSheaf_cohomology_succ
    ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (s3_fibreInclusion p y)).obj S.X₁) 0

theorem s2v_proper_finiteFibres_pushforward_preservesFiniteColimits {X Y : TopCat.{0}}
    [T2Space X] [LocallyCompactSpace X] (p : X ⟶ Y) (hp : IsProperMap p)
    (hfin : ∀ y : Y, Set.Finite {x : X | p x = y}) :
    PreservesFiniteColimits (TopCat.Sheaf.pushforward AddCommGrpCat.{0} p) := by
  let P := TopCat.Sheaf.pushforward AddCommGrpCat.{0} p
  letI : P.Additive := Functor.additive_of_preserves_binary_products P
  apply ((Functor.preservesFiniteColimits_tfae P).out 1 4).mp
  intro S hS
  have h := s2v_proper_finiteFibres_pushforward_shortExact p hp hfin hS
  exact ⟨h.exact, h.epi_g⟩

end HodgeLean.Foundations.Program
