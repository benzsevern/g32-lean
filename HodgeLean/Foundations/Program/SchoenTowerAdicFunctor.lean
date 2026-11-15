import HodgeLean.Foundations.Program.SchoenTowerAdicMaps
import Mathlib.RingTheory.Ideal.Pointwise

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped Pointwise

namespace HodgeLean.Foundations.Program

/-- The actual adic maps preserve composition of maps preserving the relevant ideals. -/
theorem s2t_adicMap_comp {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (I : Ideal A) (J : Ideal B) (K : Ideal C) (f : A →+* B) (g : B →+* C)
    (hf : I ≤ J.comap f) (hg : J ≤ K.comap g) (x : AdicCompletion I A) :
    s2t_adicMap J K g hg (s2t_adicMap I J f hf x) =
      s2t_adicMap I K (g.comp f) (fun _ ha => hg (hf ha)) x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [s2t_adicMap_eval, s2t_adicMap_eval, s2t_adicMap_eval]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← ha]
  rfl

/-- Adic maps induced by equivariant ring maps are equivariant for the induced actions. -/
theorem s2t_adicMap_action {A B G : Type*} [CommRing A] [CommRing B] [Group G]
    [MulSemiringAction G A] [MulSemiringAction G B]
    (I : Ideal A) (J : Ideal B) (f : A →+* B) (hf : I ≤ J.comap f)
    (hI : ∀ (g : G) (a : A), a ∈ I → g • a ∈ I)
    (hJ : ∀ (g : G) (b : B), b ∈ J → g • b ∈ J)
    (heq : ∀ (g : G) (a : A), f (g • a) = g • f a)
    (g : G) (x : AdicCompletion I A) :
    s2t_adicMap I J f hf (s2t_adicActionHom I hI g x) =
      s2t_adicActionHom J hJ g (s2t_adicMap I J f hf x) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [s2t_adicMap_eval, s2t_adicActionHom_eval I hI g,
    s2t_adicActionHom_eval J hJ g, s2t_adicMap_eval]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← ha]
  change Ideal.Quotient.mk (J ^ n) (f (g • a)) =
    Ideal.Quotient.mk (J ^ n) (g • f a)
  rw [heq]

/-- The induced adic action agrees with the original action on ring elements. -/
theorem s2t_adicActionHom_of {A G : Type*} [CommRing A] [Group G]
    [MulSemiringAction G A] (I : Ideal A)
    (hI : ∀ (g : G) (a : A), a ∈ I → g • a ∈ I) (g : G) (a : A) :
    s2t_adicActionHom I hI g (AdicCompletion.of I A a) =
      AdicCompletion.of I A (g • a) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [s2t_adicActionHom_eval I hI g, AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of]
  rfl

/-- Scalars commuting with the original action also commute with the actual adic action. -/
theorem s2t_adicAction_smulCommClass {R A G : Type*}
    [CommRing R] [CommRing A] [Algebra R A] [Group G]
    [MulSemiringAction G A] [SMulCommClass G R A] (I : Ideal A)
    (hI : ∀ (g : G) (a : A), a ∈ I → g • a ∈ I) :
    letI := s2t_adicAction I hI
    SMulCommClass G R (AdicCompletion I A) := by
  letI := s2t_adicAction I hI
  constructor
  intro g r x
  have hfixed : g • algebraMap R (AdicCompletion I A) r =
      algebraMap R (AdicCompletion I A) r := by
    change s2t_adicActionHom I hI g (algebraMap R (AdicCompletion I A) r) = _
    rw [AdicCompletion.algebraMap_apply, s2t_adicActionHom_of, smul_algebraMap]
  simp only [Algebra.smul_def, smul_mul', hfixed]

/-- Projection after a group action agrees with transport between the actual orbit factors. -/
theorem s2t_adicMap_action_transport {A G : Type*} [CommRing A] [Group G]
    [MulSemiringAction G A] (I J : Ideal A)
    (hI : ∀ (g : G) (a : A), a ∈ I → g • a ∈ I) (g : G)
    (hIJ : I ≤ J) (hIgJ : I ≤ g • J) (x : AdicCompletion I A) :
    s2t_adicMap I (g • J) (RingHom.id A) hIgJ (s2t_adicActionHom I hI g x) =
      s2t_adicMap J (g • J) (MulSemiringAction.toRingHom G A g) Ideal.le_comap_map
        (s2t_adicMap I J (RingHom.id A) hIJ x) := by
  change s2t_adicMap I (g • J) (RingHom.id A) hIgJ
    (s2t_adicMap I I (MulSemiringAction.toRingHom G A g) (hI g) x) = _
  rw [s2t_adicMap_comp, s2t_adicMap_comp]
  rfl

/-- Extending an ideal from an action-fixed base gives a stable ideal in the acted-on ring. -/
theorem s2t_extendedIdeal_stable {R A G : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [Group G] [MulSemiringAction G A] [SMulCommClass G R A]
    (p : Ideal R) (g : G) (a : A) (ha : a ∈ p.map (algebraMap R A)) :
    g • a ∈ p.map (algebraMap R A) := by
  let f := MulSemiringAction.toRingHom G A g
  have heq : f.comp (algebraMap R A) = algebraMap R A := by
    ext r
    exact smul_algebraMap g r
  have hmap : (p.map (algebraMap R A)).map f = p.map (algebraMap R A) := by
    rw [Ideal.map_map, heq]
  have h := Ideal.mem_map_of_mem f ha
  rwa [hmap] at h

/-- The induced adic map agrees with the original ring map on ring elements. -/
theorem s2t_adicMap_of {A B : Type*} [CommRing A] [CommRing B]
    (I : Ideal A) (J : Ideal B) (f : A →+* B) (hf : I ≤ J.comap f) (a : A) :
    s2t_adicMap I J f hf (AdicCompletion.of I A a) = AdicCompletion.of J B (f a) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [s2t_adicMap_eval, AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of]
  rfl

/-- Equal ring maps give equal actual adic maps independently of containment proofs. -/
theorem s2t_adicMap_congr {A B : Type*} [CommRing A] [CommRing B]
    (I : Ideal A) (J : Ideal B) (f g : A →+* B)
    (hf : I ≤ J.comap f) (hg : I ≤ J.comap g) (h : f = g) :
    s2t_adicMap I J f hf = s2t_adicMap I J g hg := by
  cases h
  rfl

end HodgeLean.Foundations.Program
