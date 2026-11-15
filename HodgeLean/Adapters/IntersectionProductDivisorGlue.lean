import HodgeLean.Adapters.IntersectionProductDivisorCycle

/-! # The cycle form of Fulton, Theorem 2.4, for Serre's product

For subvarieties `W = closure {w}` and `V = closure {v}` of a smooth complex variety meeting
properly, and a nonzero rational function `φ` on `W` that is a unit at every component `Z` of
`W ∩ V` and whose divisor meets `V` properly,
`[div φ] · [V] = Σ_Z i(Z; W · V) [div (φ|_Z)]` (`a3z_principal_intersect`), so it is rationally
equivalent to zero. The proof glues the local identity `a3y_principal_at` over the points `T` of
`W ∩ V` of codimension one more than the components, writing `φ = a / b` with `a`, `b` in
`𝒪_{X,T}` outside the primes of the components through `T` (prime avoidance,
`a3z_exists_num_den`).

Source: Fulton, *Intersection Theory*, second edition, Theorem 2.4 and §2.3 (intersecting a
principal divisor with a subvariety), and Example 7.1.2; Serre, *Algèbre locale, multiplicités*,
Chapitre V. HC no distance; AV milestone no distance.
-/

open CategoryTheory AlgebraicGeometry IsLocalRing Order

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace HodgeLean.Adapters
universe u

section germ
variable {X : Scheme.{u}} (w : X)

/-- A point of `closure {w}` is the image of a point of `W`. -/
theorem a3z_exists_pt {z : X} (hw : w ⤳ z) :
    ∃ zW : cycleComponent X w, cycleComponentι X w zW = z := by
  have : z ∈ Set.range (cycleComponentι X w) := by
    rw [range_cycleComponentι]
    exact specializes_iff_mem_closure.1 hw
  exact this

/-- `W → X` reflects specializations. -/
theorem a3z_specializes_iff (x y : cycleComponent X w) :
    x ⤳ y ↔ cycleComponentι X w x ⤳ cycleComponentι X w y :=
  ((cycleComponentι X w).isClosedEmbedding.isInducing.specializes_iff).symm

/-- The restriction to `K(W)` commutes with specialization of germs. -/
theorem a3z_germ_specializes {z T : X} (zW TW : cycleComponent X w)
    (hz : cycleComponentι X w zW = z) (hT : cycleComponentι X w TW = T) (hzT : z ⤳ T)
    (a : X.presheaf.stalk T) :
    a3y_germ w TW hT a = a3y_germ w zW hz ((X.presheaf.stalkSpecializes hzT).hom a) := by
  subst hz hT
  have h : zW ⤳ TW := (a3z_specializes_iff w zW TW).2 hzT
  rw [a3y_germ_self, a3y_germ_self, ← a3y_algebraMap_stalkSpecializes h]
  congr 1
  exact (Scheme.Hom.stalkSpecializes_stalkMap_apply (cycleComponentι X w) zW TW h a).symm

/-- A rational function `φ` on `W = closure {w}` is a unit at the point `z` of `W`: it is a
quotient of two units of `𝒪_{X,z}` restricted to `W`.
Source: Fulton, *Intersection Theory*, second edition, §1.2 and §2.3 (`φ` is a unit in the local
ring `𝒪_{W,Z}`). -/
def a3z_UnitAt (φ : (cycleComponent X w).functionField) (z : X) : Prop :=
  ∃ (zW : cycleComponent X w) (hz : cycleComponentι X w zW = z) (a b : X.presheaf.stalk z),
    a ∉ maximalIdeal (X.presheaf.stalk z) ∧ b ∉ maximalIdeal (X.presheaf.stalk z) ∧
      a3y_germ w zW hz a = φ * a3y_germ w zW hz b

example (zW : cycleComponent X w) : a3z_UnitAt w 1 (cycleComponentι X w zW) :=
  ⟨zW, rfl, 1, 1, fun h => (maximalIdeal.isMaximal _).ne_top (Ideal.eq_top_of_isUnit_mem _ h
    isUnit_one), fun h => (maximalIdeal.isMaximal _).ne_top (Ideal.eq_top_of_isUnit_mem _ h
    isUnit_one), by simp⟩

/-- In `𝒪_{X,z}`, two restrictions to `W` agree exactly when the difference lies in `𝔭_W`. -/
theorem a3z_germ_eq_iff {z : X} (zW : cycleComponent X w) (hz : cycleComponentι X w zW = z)
    (a b : X.presheaf.stalk z) :
    a3y_germ w zW hz a = a3y_germ w zW hz b ↔ a - b ∈ a3i_stalkIdeal X z w := by
  rw [← a3y_germ_eq_zero_iff w zW hz, map_sub, sub_eq_zero]

/-- The prime of `w` lies in the maximal ideal of `𝒪_{X,z}` for `w ⤳ z`. -/
theorem a3z_stalkIdeal_le_maximalIdeal {z : X} (hw : w ⤳ z) :
    a3i_stalkIdeal X z w ≤ maximalIdeal (X.presheaf.stalk z) :=
  le_maximalIdeal (a3q_stalkIdeal_isPrime X hw).ne_top

end germ

section avoid
variable {X : Scheme.{u}} (w : X)

/-- Prime avoidance for a rational function that is a unit along finitely many points `z` of `W`
through `T`: `φ = a / b` on `W` with `a`, `b ∈ 𝒪_{X,T}` outside every prime `𝔭_z`. -/
theorem a3z_exists_num_den {T : X} (TW : cycleComponent X w) (hT : cycleComponentι X w TW = T)
    (φ : (cycleComponent X w).functionField) (Zs : Finset X) (hZs : ∀ z ∈ Zs, z ⤳ T)
    (hunit : ∀ z ∈ Zs, a3z_UnitAt w φ z) :
    ∃ a b : X.presheaf.stalk T, (∀ z ∈ Zs, a ∉ a3i_stalkIdeal X T z ∧
      b ∉ a3i_stalkIdeal X T z) ∧ a3y_germ w TW hT a = φ * a3y_germ w TW hT b := by
  classical
  set g := a3y_germ w TW hT
  let I : Ideal (X.presheaf.stalk T) :=
    { carrier := {b | ∃ a, g a = φ * g b}
      add_mem' := by
        rintro b b' ⟨a, ha⟩ ⟨a', ha'⟩
        exact ⟨a + a', by rw [map_add, map_add, ha, ha', mul_add]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c b ⟨a, ha⟩
        exact ⟨c * a, by rw [smul_eq_mul, map_mul, map_mul, ha]; ring⟩ }
  -- `I` is contained in no `𝔭_z`
  have hI : ∀ z ∈ Zs, ¬ (I : Set (X.presheaf.stalk T)) ⊆ a3i_stalkIdeal X T z := by
    intro z hzZ hsub
    have h := hZs z hzZ
    obtain ⟨zW, hz, az, bz, haz, hbz, he⟩ := hunit z hzZ
    let := (X.presheaf.stalkSpecializes h).hom.toAlgebra
    have := a3q_stalkIdeal_isPrime X h
    have := a3q_isLocalization_stalkSpecializes X h
    have hW : w ⤳ z := by
      have := (genericPoint_spec (cycleComponent X w)).specializes (Set.mem_univ zW)
      have := this.map (cycleComponentι X w).continuous
      rwa [a3m_cycleComponentι_genericPoint, hz] at this
    have hgz : ∀ r, g r = a3y_germ w zW hz (algebraMap _ _ r) := fun r =>
      a3z_germ_specializes w zW TW hz hT h r
    obtain ⟨⟨a₀, s⟩, rfl⟩ := IsLocalization.mk'_surjective (a3i_stalkIdeal X T z).primeCompl az
    obtain ⟨⟨b₀, s'⟩, rfl⟩ := IsLocalization.mk'_surjective (a3i_stalkIdeal X T z).primeCompl bz
    dsimp only at haz hbz he
    have hb₀ : b₀ ∉ a3i_stalkIdeal X T z := by
      intro hb
      apply hbz
      rw [IsLocalization.AtPrime.mk'_mem_maximal_iff (X.presheaf.stalk z)
        (a3i_stalkIdeal X T z)]
      exact hb
    -- `b₀ s` lies in `I`
    have hmem : b₀ * s ∈ I := by
      refine ⟨a₀ * s', ?_⟩
      have e1 : algebraMap _ (X.presheaf.stalk z) (a₀ * s') =
          IsLocalization.mk' (X.presheaf.stalk z) a₀ s *
            algebraMap (X.presheaf.stalk T) (X.presheaf.stalk z)
              ((s : X.presheaf.stalk T) * (s' : X.presheaf.stalk T)) := by
        rw [map_mul, map_mul, ← mul_assoc, IsLocalization.mk'_spec_mk]
      have e2 : algebraMap _ (X.presheaf.stalk z) (b₀ * s) =
          IsLocalization.mk' (X.presheaf.stalk z) b₀ s' *
            algebraMap (X.presheaf.stalk T) (X.presheaf.stalk z)
              ((s : X.presheaf.stalk T) * (s' : X.presheaf.stalk T)) := by
        rw [map_mul, map_mul, mul_comm (algebraMap _ _ (s : X.presheaf.stalk T)), ← mul_assoc,
          IsLocalization.mk'_spec_mk]
      rw [hgz, hgz, e1, e2]
      simp only [map_mul, he]
      ring
    have := hsub hmem
    rcases (a3q_stalkIdeal_isPrime X h).mem_or_mem this with h1 | h1
    · exact hb₀ h1
    · exact s.2 h1
  -- prime avoidance
  have hprime : ∀ z ∈ Zs, (a3i_stalkIdeal X T z).IsPrime := fun z hz =>
    a3q_stalkIdeal_isPrime X (hZs z hz)
  obtain ⟨b, hbI, hbZ⟩ : ∃ b ∈ I, ∀ z ∈ Zs, b ∉ a3i_stalkIdeal X T z := by
    by_contra hcon
    push Not at hcon
    have hsub : (I : Set (X.presheaf.stalk T)) ⊆
        ⋃ z ∈ (↑Zs : Set X), (a3i_stalkIdeal X T z : Set (X.presheaf.stalk T)) := by
      intro b hb
      obtain ⟨z, hz, hbz⟩ := hcon b hb
      exact Set.mem_biUnion hz hbz
    obtain ⟨z, hz, hle⟩ := (Ideal.subset_union_prime (s := Zs)
      (f := fun z => a3i_stalkIdeal X T z) T T (fun z hz _ _ => hprime z hz)).mp hsub
    exact hI z hz hle
  obtain ⟨a, ha⟩ := hbI
  refine ⟨a, b, fun z hzZ => ⟨fun haz => ?_, hbZ z hzZ⟩, ha⟩
  -- `a ∉ 𝔭_z`: otherwise `b · a_z ∈ 𝔪_z`
  have h := hZs z hzZ
  obtain ⟨zW, hz, az, bz, haz', hbz', he⟩ := hunit z hzZ
  have hW : w ⤳ z := by
    have := (genericPoint_spec (cycleComponent X w)).specializes (Set.mem_univ zW)
    have := this.map (cycleComponentι X w).continuous
    rwa [a3m_cycleComponentι_genericPoint, hz] at this
  set σ := (X.presheaf.stalkSpecializes h).hom
  have hgz : ∀ r, g r = a3y_germ w zW hz (σ r) := fun r => a3z_germ_specializes w zW TW hz hT h r
  have hrel : a3y_germ w zW hz (σ a * bz) = a3y_germ w zW hz (σ b * az) := by
    rw [map_mul, map_mul, ← hgz, ← hgz, ha, he]
    ring
  rw [a3z_germ_eq_iff] at hrel
  have hm := a3z_stalkIdeal_le_maximalIdeal w hW hrel
  have hσ : ∀ r, σ r ∈ maximalIdeal (X.presheaf.stalk z) ↔ r ∈ a3i_stalkIdeal X T z := by
    intro r
    let := σ.toAlgebra
    have := a3q_stalkIdeal_isPrime X h
    have := a3q_isLocalization_stalkSpecializes X h
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk z)
      (a3i_stalkIdeal X T z) r
  have h1 : σ a * bz ∈ maximalIdeal (X.presheaf.stalk z) :=
    Ideal.mul_mem_right _ _ ((hσ a).2 haz)
  have h2 : σ b * az ∈ maximalIdeal (X.presheaf.stalk z) := by
    have := Ideal.sub_mem _ h1 hm
    rwa [sub_sub_cancel] at this
  rcases (maximalIdeal.isMaximal _).isPrime.mem_or_mem h2 with h3 | h3
  · exact hbZ z hzZ ((hσ b).1 h3)
  · exact haz' h3

end avoid

section restriction
variable {X : Scheme.{u}} (w : X)

/-- The restriction to `K(Z)` of germs at `z`, for `Z = closure {z}`.
Source: Hartshorne, *Algebraic Geometry*, II, Exercise 3.11 (the closed subscheme
`closure {z}`) and Proposition 2.2 (stalks). -/
abbrev a3z_germZ (z : X) : X.presheaf.stalk z →+* (cycleComponent X z).functionField :=
  a3y_germ z (genericPoint (cycleComponent X z)) (a3m_cycleComponentι_genericPoint X z)

example (z : X) : a3z_germZ z 1 = 1 := map_one _

/-- `ψ ∈ K(Z)` is the restriction of `φ ∈ K(W)` to `Z = closure {z} ⊆ W`: for some units `a`, `b` of
`𝒪_{X,z}`, `φ = a / b` on `W` and `ψ = a / b` on `Z`.
Source: Fulton, *Intersection Theory*, second edition, §2.3 (the restriction `φ|_Z` of a rational
function that is a unit along `Z`). -/
def a3z_IsRestriction (φ : (cycleComponent X w).functionField) (z : X)
    (ψ : (cycleComponent X z).functionField) : Prop :=
  ∃ (zW : cycleComponent X w) (hz : cycleComponentι X w zW = z) (a b : X.presheaf.stalk z),
    a ∉ maximalIdeal (X.presheaf.stalk z) ∧ b ∉ maximalIdeal (X.presheaf.stalk z) ∧
      a3y_germ w zW hz a = φ * a3y_germ w zW hz b ∧ a3z_germZ z a = ψ * a3z_germZ z b

example (zW : cycleComponent X w) :
    a3z_IsRestriction w 1 (cycleComponentι X w zW) 1 :=
  ⟨zW, rfl, 1, 1, fun h => (maximalIdeal.isMaximal _).ne_top (Ideal.eq_top_of_isUnit_mem _ h
    isUnit_one), fun h => (maximalIdeal.isMaximal _).ne_top (Ideal.eq_top_of_isUnit_mem _ h
    isUnit_one), by simp, by simp⟩

/-- Restrictions to `K(Z)` vanish exactly on the maximal ideal of `𝒪_{X,z}`. -/
theorem a3z_germZ_eq_zero_iff (z : X) (a : X.presheaf.stalk z) :
    a3z_germZ z a = 0 ↔ a ∈ maximalIdeal (X.presheaf.stalk z) := by
  rw [a3y_germ_eq_zero_iff, a3c_stalkIdeal_self]

theorem a3z_isRestriction_unitAt {φ : (cycleComponent X w).functionField} {z : X}
    {ψ : (cycleComponent X z).functionField} (h : a3z_IsRestriction w φ z ψ) :
    a3z_UnitAt w φ z :=
  let ⟨zW, hz, a, b, ha, hb, he, _⟩ := h
  ⟨zW, hz, a, b, ha, hb, he⟩

/-- A rational function that is a unit at `z` has a restriction to `Z = closure {z}`. -/
theorem a3z_exists_restriction {φ : (cycleComponent X w).functionField} {z : X}
    (h : a3z_UnitAt w φ z) : ∃ ψ, ψ ≠ 0 ∧ a3z_IsRestriction w φ z ψ := by
  obtain ⟨zW, hz, a, b, ha, hb, he⟩ := h
  have hb0 : a3z_germZ z b ≠ 0 := fun h0 => hb ((a3z_germZ_eq_zero_iff z b).1 h0)
  have ha0 : a3z_germZ z a ≠ 0 := fun h0 => ha ((a3z_germZ_eq_zero_iff z a).1 h0)
  refine ⟨a3z_germZ z a / a3z_germZ z b, div_ne_zero ha0 hb0,
    zW, hz, a, b, ha, hb, he, ?_⟩
  rw [div_mul_cancel₀ _ hb0]

/-- The restriction is read at any point `T` of `Z` through a quotient `a / b` of germs at `T`
representing `φ` on `W`. -/
theorem a3z_restriction_at {φ : (cycleComponent X w).functionField} {z T : X}
    {ψ : (cycleComponent X z).functionField} (hψ : a3z_IsRestriction w φ z ψ) (hzT : z ⤳ T)
    (TW : cycleComponent X w) (hTW : cycleComponentι X w TW = T)
    (TZ : cycleComponent X z) (hTZ : cycleComponentι X z TZ = T)
    (a b : X.presheaf.stalk T) (hab : a3y_germ w TW hTW a = φ * a3y_germ w TW hTW b) :
    a3y_germ z TZ hTZ a = ψ * a3y_germ z TZ hTZ b := by
  obtain ⟨zW, hz, az, bz, haz, hbz, heW, heZ⟩ := hψ
  have hW : w ⤳ z := by
    have := (genericPoint_spec (cycleComponent X w)).specializes (Set.mem_univ zW)
    have := this.map (cycleComponentι X w).continuous
    rwa [a3m_cycleComponentι_genericPoint, hz] at this
  set σ := (X.presheaf.stalkSpecializes hzT).hom
  have hgW : ∀ r, a3y_germ w TW hTW r = a3y_germ w zW hz (σ r) := fun r =>
    a3z_germ_specializes w zW TW hz hTW hzT r
  have hgZ : ∀ r, a3y_germ z TZ hTZ r = a3z_germZ z (σ r) := fun r =>
    a3z_germ_specializes z _ TZ (a3m_cycleComponentι_genericPoint X z) hTZ hzT r
  have hrel : a3y_germ w zW hz (σ a * bz) = a3y_germ w zW hz (σ b * az) := by
    rw [map_mul, map_mul, ← hgW, ← hgW, hab, heW]
    ring
  rw [a3z_germ_eq_iff] at hrel
  have hm := a3z_stalkIdeal_le_maximalIdeal w hW hrel
  have hZ : a3z_germZ z (σ a * bz) = a3z_germZ z (σ b * az) := by
    rw [← sub_eq_zero, ← map_sub, a3z_germZ_eq_zero_iff]
    exact hm
  have hbz0 : a3z_germZ z bz ≠ 0 := fun h0 => hbz ((a3z_germZ_eq_zero_iff z bz).1 h0)
  rw [hgZ, hgZ]
  rw [map_mul, map_mul, heZ] at hZ
  apply mul_right_cancel₀ hbz0
  rw [hZ]
  ring

end restriction

section coeff
variable (X : Scheme.{u})

open Classical in
/-- The coefficient of `c · [V]` at a point: `Σ_u c(u) · (closure {u} · V)(T)`. -/
theorem a3z_intersect_single_apply (c : AlgebraicCycle X ℚ) (v : X) (s : Finset X)
    (hs : ∀ u ∉ s, c u = 0) (T : X) :
    a3i_intersect X c (Function.locallyFinsuppWithin.single v 1) T =
      ∑ u ∈ s, c u * a3i_intersectPrime X u v T := by
  classical
  have ht : ∀ v' ∉ ({v} : Finset X), (Function.locallyFinsuppWithin.single v (1 : ℚ)) v' = 0 := by
    intro v' hv'
    rw [Finset.mem_singleton] at hv'
    rw [Function.locallyFinsuppWithin.single_apply, ite_eq_right_iff]
    exact fun h => absurd h hv'
  rw [a3c_intersect_eq_sum X c _ s {v} hs ht, Function.locallyFinsuppWithin.coe_sum,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_singleton, Function.locallyFinsuppWithin.mapRange_apply,
    Function.locallyFinsuppWithin.single_apply, ite_eq_left_iff.2 (fun h => absurd rfl h), mul_one]

variable [IsNoetherian X]

/-- A point with a nonzero coefficient in `[div φ]` is a codimension-one point of `W`. -/
theorem a3z_principalCycle_ne_zero (w : X) (φ : (cycleComponent X w).functionField)
    (hφ : φ ≠ 0) (u : X) (hu : a2_principalCycle X ℚ w φ u ≠ 0) :
    ∃ D : cycleComponent X w, cycleComponentι X w D = u ∧ coheight D = 1 ∧
      a2_principalCycle X ℚ w φ u = ((cycleComponent X w).ord φ D : ℚ) := by
  by_cases hr : u ∈ Set.range (cycleComponentι X w)
  · obtain ⟨D, rfl⟩ := hr
    refine ⟨D, rfl, ?_, a3y_principalCycle_apply X w φ hφ D⟩
    by_contra h1
    rw [a3y_principalCycle_apply X w φ hφ D, Scheme.ord_eq_zero_of_coheight_neq_one h1] at hu
    exact hu (by simp)
  · exact absurd (a3y_principalCycle_apply_of_not_mem X w φ u hr) hu

/-- A nonzero coefficient of `closure {u} · closure {v}` sits at a component of the intersection. -/
theorem a3z_intersectPrime_ne_zero (u v T : X) (h : a3i_intersectPrime X u v T ≠ 0) :
    T ∈ a3y_comps u v := by
  classical
  rw [a3y_intersectPrime_apply] at h
  split_ifs at h with hex
  · exact hex
  · exact absurd rfl h

/-- For properly meeting `closure {u}` and `closure {v}`, a common specialization `T` of
codimension `codim u + codim v` is a component, so the coefficient there is Serre's
multiplicity. -/
theorem a3z_intersectPrime_apply_of_proper (u v T : X) (huv : a3i_MeetProperly X u v)
    (hu : u ⤳ T) (hv : v ⤳ T) (hT : coheight T = coheight u + coheight v) :
    a3i_intersectPrime X u v T = (a3i_serreMult X T u v : ℚ) := by
  classical
  rw [a3y_intersectPrime_apply, ite_eq_left_of_eq_true _ _ (eq_true ?_)]
  refine a3y_component_of_maximal u v T hu hv fun q huq hvq hqT => ?_
  obtain ⟨z, hz, hzq⟩ := a3y_exists_comp u v huq hvq
  have hzT : z = T := by
    refine a3y_eq_of_specializes (hzq.trans hqT) ?_
    rw [a3y_coheight_comps u v huv hz, hT]
  subst hzT
  exact (hqT.antisymm hzq).eq

end coeff

section point

/-- `QuotSMulTop a M` is killed by `a`. -/
theorem a3z_smul_quotSMulTop {A : Type*} [CommRing A] (a : A) (M : Type*) [AddCommGroup M]
    [Module A M] (n : QuotSMulTop a M) : a • n = 0 := by
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ n
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_pointwise_smul m a ⊤ trivial

theorem a3z_isRestriction_ne_zero {X : Scheme.{u}} (w : X)
    {φ : (cycleComponent X w).functionField} {z : X} {ψ : (cycleComponent X z).functionField}
    (h : a3z_IsRestriction w φ z ψ) : ψ ≠ 0 := by
  rintro rfl
  obtain ⟨_, _, a, _, ha, _, _, he⟩ := h
  rw [zero_mul, a3z_germZ_eq_zero_iff] at he
  exact ha he

/-- `w` specializes to every point of `W = closure {w}`. -/
theorem a3z_specializes_pt {X : Scheme.{u}} (w : X) (D : cycleComponent X w) :
    w ⤳ cycleComponentι X w D := by
  have := (genericPoint_spec (cycleComponent X w)).specializes (Set.mem_univ D)
  have := this.map (cycleComponentι X w).continuous
  rwa [a3m_cycleComponentι_genericPoint] at this

/-- Serre's multiplicity at `T` as the truncated Euler characteristic `a3s_chi` at the codimension
of `T`. -/
theorem a3z_serreMult_eq_chi {X : Scheme.{u}} (T u v : X) (m : ℕ) (hm : (m : ℕ∞) = coheight T) :
    a3i_serreMult X T u v = a3s_chi m
      (ModuleCat.of (X.presheaf.stalk T) (X.presheaf.stalk T ⧸ a3i_stalkIdeal X T u))
      (ModuleCat.of (X.presheaf.stalk T) (X.presheaf.stalk T ⧸ a3i_stalkIdeal X T v)) := by
  unfold a3i_serreMult a3s_chi
  rw [← hm, ENat.toNat_natCast]
  rfl

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsNoetherian X.left]
  (w v : X.left)

omit [AlgebraicGeometry.IsNoetherian X.left] in
/-- For a prime `𝔇` of `𝒪_{X,T}` over `𝔭_W` with `dim 𝒪_{X,T}/𝔇 + 1 = dim 𝒪_{X,T}/𝔭_W`, the point
of `X` over `𝔇` is a codimension-one point of `W`. -/
theorem a3z_codimOne_of_prime {T : X.left} (hwT : w ⤳ T) (TW : cycleComponent X.left w)
    (hTW : cycleComponentι X.left w TW = T) (𝔇 : PrimeSpectrum (X.left.presheaf.stalk T))
    (h1 : a3i_stalkIdeal X.left T w ≤ 𝔇.asIdeal)
    (h2 : ringKrullDim (X.left.presheaf.stalk T ⧸ 𝔇.asIdeal) + 1 =
      ringKrullDim (X.left.presheaf.stalk T ⧸ a3i_stalkIdeal X.left T w)) :
    ∃ D : cycleComponent X.left w, cycleComponentι X.left w D = X.left.fromSpecStalk T 𝔇 ∧
      coheight D = 1 ∧ D ⤳ TW ∧
        a3i_stalkIdeal X.left T (cycleComponentι X.left w D) = 𝔇.asIdeal := by
  set u := X.left.fromSpecStalk T 𝔇
  have hu : u ⤳ T := a3y_specializes_fromSpecStalk T 𝔇
  have hpt : a3i_stalkIdeal X.left T u = 𝔇.asIdeal :=
    congrArg PrimeSpectrum.asIdeal (a3y_pt_fromSpecStalk T 𝔇)
  have hwu : w ⤳ u := by
    rw [← a3y_pt_le_iff T w u hwT hu]
    change a3i_stalkIdeal X.left T w ≤ a3i_stalkIdeal X.left T u
    rw [hpt]
    exact h1
  obtain ⟨D, hD⟩ := a3z_exists_pt w hwu
  refine ⟨D, hD, ?_, ?_, by rw [hD, hpt]⟩
  · rw [a3y_coheight_eq_one_iff X w D, hD]
    obtain ⟨cu, ct, nu, hcu, hct, hnu, hu'⟩ := a3y_dims X hu
    obtain ⟨cw, ct', nw, hcw, hct', hnw, hw'⟩ := a3y_dims X hwT
    rw [hpt] at hnu
    rw [hnu, hnw] at h2
    have h2' : nu + 1 = nw := by exact_mod_cast h2
    rw [hct] at hct'
    have : ct' = ct := by exact_mod_cast hct'.symm
    rw [hcu, hcw]
    norm_cast
    omega
  · rw [a3z_specializes_iff, hD, hTW]
    exact hu

/-- The local identity at one point `T` of `W ∩ V` of codimension one more than the components
through it, in terms of the coefficients of `[div φ]`, of the intersection cycles and of the
`[div (φ|_Z)]`. Only the components of `W ∩ V` through `T` need the expected codimension. -/
theorem a3z_principal_point (T : X.left) (hwT : w ⤳ T) (hvT : v ⤳ T)
    (hloc : ∀ z ∈ a3y_comps w v, z ⤳ T → coheight z = coheight w + coheight v)
    (hT : coheight T = coheight w + coheight v + 1)
    (φ : (cycleComponent X.left w).functionField) (hφ : φ ≠ 0)
    (hD : ∀ d, a2_principalCycle X.left ℚ w φ d ≠ 0 → a3i_MeetProperly X.left d v)
    (ψ : (z : X.left) → (cycleComponent X.left z).functionField)
    (hψ : ∀ z ∈ a3y_comps w v, a3z_IsRestriction w φ z (ψ z))
    (s : Finset X.left) (hs : ∀ u ∉ s, a2_principalCycle X.left ℚ w φ u = 0) :
    ∑ u ∈ s, a2_principalCycle X.left ℚ w φ u * a3i_intersectPrime X.left u v T =
      ∑ z ∈ a3y_compsAt X w v T,
        (a3i_serreMult X.left z w v : ℚ) * a2_principalCycle X.left ℚ z (ψ z) T := by
  classical
  set c := a2_principalCycle X.left ℚ w φ with hc
  set A := X.left.presheaf.stalk T
  have hP := a3q_stalkIdeal_isPrime X.left hwT
  have hQ := a3q_stalkIdeal_isPrime X.left hvT
  have hmem : ∀ z, z ∈ a3y_compsAt X w v T ↔ z ∈ a3y_comps w v ∧ z ⤳ T := fun z => by
    simp only [a3y_compsAt, Finset.mem_filter, Set.Finite.mem_toFinset]
  obtain ⟨TW, hTW⟩ := a3z_exists_pt w hwT
  obtain ⟨a, b, habZ, hab⟩ := a3z_exists_num_den w TW hTW φ (a3y_compsAt X w v T)
    (fun z hz => ((hmem z).1 hz).2)
    (fun z hz => a3z_isRestriction_unitAt w (hψ z ((hmem z).1 hz).1))
  obtain ⟨z₀, hz₀, hz₀T⟩ := a3y_exists_comp w v hwT hvT
  have hz₀m : z₀ ∈ a3y_compsAt X w v T := (hmem z₀).2 ⟨hz₀, hz₀T⟩
  have hwz₀ : a3i_stalkIdeal X.left T w ≤ a3i_stalkIdeal X.left T z₀ :=
    (a3y_pt_le_iff T w z₀ hwT hz₀T).2 (a3y_comps_spec w v hz₀).1
  have ha : a ∉ a3i_stalkIdeal X.left T w := fun h => (habZ z₀ hz₀m).1 (hwz₀ h)
  have hb : b ∉ a3i_stalkIdeal X.left T w := fun h => (habZ z₀ hz₀m).2 (hwz₀ h)
  have hga : a3y_germ w TW hTW a ≠ 0 := fun h0 => ha ((a3y_germ_eq_zero_iff w TW hTW a).1 h0)
  have hgb : a3y_germ w TW hTW b ≠ 0 := fun h0 => hb ((a3y_germ_eq_zero_iff w TW hTW b).1 h0)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (a3c_coheight_ne_top X.left T)
  have hfin : ∀ 𝔮 : PrimeSpectrum A, ∃ n : ℕ, ringKrullDim (A ⧸ 𝔮.asIdeal) = n := fun 𝔮 => by
    obtain ⟨n, hn, -⟩ := a3w_dim_quot_nat X T 𝔮.asIdeal
    exact ⟨n, hn⟩
  obtain ⟨Fa, hFa⟩ := a3y_exists_F _ a ha hfin
  obtain ⟨Fb, hFb⟩ := a3y_exists_F _ b hb hfin
  have keya := a3y_principal_at X w v T hwT hvT hloc hT a ha (fun z hz => (habZ z hz).1) Fa hFa m
    hm.symm.le
  have keyb := a3y_principal_at X w v T hwT hvT hloc hT b hb (fun z hz => (habZ z hz).2) Fb hFb m
    hm.symm.le
  -- the right side
  have hR : ∀ z ∈ a3y_compsAt X w v T, a2_principalCycle X.left ℚ z (ψ z) T =
      ((a3e_herbrand a (A ⧸ a3i_stalkIdeal X.left T z) -
        a3e_herbrand b (A ⧸ a3i_stalkIdeal X.left T z) : ℤ) : ℚ) := by
    intro z hz
    obtain ⟨hzc, hzT⟩ := (hmem z).1 hz
    obtain ⟨TZ, hTZ⟩ := a3z_exists_pt z hzT
    have hcoh : coheight TZ = 1 := by
      rw [a3y_coheight_eq_one_iff X z TZ, hTZ, hT, hloc z hzc hzT]
    have hψz := hψ z hzc
    have hψ0 : ψ z ≠ 0 := a3z_isRestriction_ne_zero w hψz
    have happ := a3y_principalCycle_apply X.left z (ψ z) hψ0 TZ
    rw [hTZ] at happ
    rw [happ]
    have hrel := a3z_restriction_at w hψz hzT TW hTW TZ hTZ a b hab
    have hga' : a3y_germ z TZ hTZ a ≠ 0 := fun h0 =>
      (habZ z hz).1 ((a3y_germ_eq_zero_iff z TZ hTZ a).1 h0)
    have hgb' : a3y_germ z TZ hTZ b ≠ 0 := fun h0 =>
      (habZ z hz).2 ((a3y_germ_eq_zero_iff z TZ hTZ b).1 h0)
    have hord : (cycleComponent X.left z).ord (ψ z) TZ =
        (cycleComponent X.left z).ord (a3y_germ z TZ hTZ a) TZ -
          (cycleComponent X.left z).ord (a3y_germ z TZ hTZ b) TZ := by
      rw [hrel, Scheme.ord_mul hψ0 hgb']
      ring
    rw [hord, a3y_ord_germ_self z TZ hTZ hcoh a (habZ z hz).1,
      a3y_ord_germ_self z TZ hTZ hcoh b (habZ z hz).2]
  have hRsum : ∑ z ∈ a3y_compsAt X w v T,
      (a3i_serreMult X.left z w v : ℚ) * a2_principalCycle X.left ℚ z (ψ z) T =
      ∑ z ∈ a3y_compsAt X w v T, (a3i_serreMult X.left z w v : ℚ) *
        ((a3e_herbrand a (A ⧸ a3i_stalkIdeal X.left T z) -
          a3e_herbrand b (A ⧸ a3i_stalkIdeal X.left T z) : ℤ) : ℚ) :=
    Finset.sum_congr rfl fun z hz => by rw [hR z hz]
  rw [hRsum]
  -- the left side, over the primes of `𝒪_{X,T}`
  set La : PrimeSpectrum A → ℤ := fun 𝔇 =>
    ((a3e_locLen 𝔇 (QuotSMulTop a (A ⧸ a3i_stalkIdeal X.left T w))).toNat : ℤ) with hLa
  set Lb : PrimeSpectrum A → ℤ := fun 𝔇 =>
    ((a3e_locLen 𝔇 (QuotSMulTop b (A ⧸ a3i_stalkIdeal X.left T w))).toNat : ℤ) with hLb
  set χ : PrimeSpectrum A → ℤ := fun 𝔇 => a3s_chi m (ModuleCat.of A (A ⧸ 𝔇.asIdeal))
    (ModuleCat.of A (A ⧸ a3i_stalkIdeal X.left T v)) with hχ
  set s' := s.filter (fun u => c u ≠ 0 ∧ u ⤳ T) with hs'def
  set G := Fa ∪ Fb ∪ s'.image (a3y_ptOr X T) with hGdef
  have hpt : ∀ u (h : u ⤳ T), a3y_ptOr X T u = a3y_pt T u h := fun u h => by
    simp [a3y_ptOr, h]
  have hs'mem : ∀ u ∈ s', u ∈ s ∧ c u ≠ 0 ∧ u ⤳ T := fun u hu => by
    simpa [hs'def] using hu
  have hcoh : ∀ u, c u ≠ 0 → ∃ D : cycleComponent X.left w, cycleComponentι X.left w D = u ∧
      coheight D = 1 ∧ coheight u = coheight w + 1 ∧ w ⤳ u := by
    intro u hcu
    obtain ⟨D, hD, hD1, -⟩ := a3z_principalCycle_ne_zero X.left w φ hφ u hcu
    refine ⟨D, hD, hD1, ?_, hD ▸ a3z_specializes_pt w D⟩
    rw [← hD]
    exact (a3y_coheight_eq_one_iff X w D).1 hD1
  have hGprop : ∀ 𝔇 ∈ G, a3i_stalkIdeal X.left T w ≤ 𝔇.asIdeal ∧
      ringKrullDim (A ⧸ 𝔇.asIdeal) + 1 = ringKrullDim (A ⧸ a3i_stalkIdeal X.left T w) := by
    intro 𝔇 h𝔇
    rcases Finset.mem_union.1 h𝔇 with h | h
    · rcases Finset.mem_union.1 h with h | h
      · obtain ⟨h1, -, h2⟩ := (hFa 𝔇).1 h
        exact ⟨h1, h2⟩
      · obtain ⟨h1, -, h2⟩ := (hFb 𝔇).1 h
        exact ⟨h1, h2⟩
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 h
      obtain ⟨-, hcu, huT⟩ := hs'mem u hu
      obtain ⟨D, hD, hD1, hcohu, hwu⟩ := hcoh u hcu
      rw [hpt u huT]
      refine ⟨(a3y_pt_le_iff T w u hwT huT).2 hwu, ?_⟩
      obtain ⟨cu, ct, nu, hcu', hct, hnu, hsum⟩ := a3y_dims X huT
      obtain ⟨cw, ct', nw, hcw, hct', hnw, hsum'⟩ := a3y_dims X hwT
      change ringKrullDim (A ⧸ a3i_stalkIdeal X.left T u) + 1 = _
      rw [hnu, hnw]
      rw [hcu', hcw] at hcohu
      rw [hct] at hct'
      have h1 : cu = cw + 1 := by exact_mod_cast hcohu
      have h2 : ct' = ct := by exact_mod_cast hct'.symm
      norm_cast
      omega
  -- each prime of `G` is a codimension-one point of `W`, and the terms match
  have hterm : ∀ 𝔇 ∈ G, (((La 𝔇 - Lb 𝔇 : ℤ) * χ 𝔇 : ℤ) : ℚ) =
      c (X.left.fromSpecStalk T 𝔇) * (a3i_serreMult X.left T (X.left.fromSpecStalk T 𝔇) v : ℚ) := by
    intro 𝔇 h𝔇
    obtain ⟨D, hD, hD1, hDT, hst⟩ :=
      a3z_codimOne_of_prime X w hwT TW hTW 𝔇 (hGprop 𝔇 h𝔇).1 (hGprop 𝔇 h𝔇).2
    have hp𝔇 : (⟨a3i_stalkIdeal X.left T (cycleComponentι X.left w D),
        a3q_stalkIdeal_isPrime X.left (hTW ▸ hDT.map (cycleComponentι X.left w).continuous)⟩ :
          PrimeSpectrum A) = 𝔇 := PrimeSpectrum.ext hst
    have ea := a3y_ord_germ w TW D hTW hDT hD1 a ha
    have eb := a3y_ord_germ w TW D hTW hDT hD1 b hb
    rw [hp𝔇] at ea eb
    have hφD : (cycleComponent X.left w).ord φ D =
        (cycleComponent X.left w).ord (a3y_germ w TW hTW a) D -
          (cycleComponent X.left w).ord (a3y_germ w TW hTW b) D := by
      rw [hab, Scheme.ord_mul hφ hgb]
      ring
    have hcD : c (X.left.fromSpecStalk T 𝔇) = ((cycleComponent X.left w).ord φ D : ℚ) := by
      rw [← hD]
      exact a3y_principalCycle_apply X.left w φ hφ D
    have hSM : a3i_serreMult X.left T (X.left.fromSpecStalk T 𝔇) v = χ 𝔇 := by
      rw [a3z_serreMult_eq_chi T _ v m hm, ← hD, hst]
    rw [hcD, hSM, hφD, ea, eb]
    simp only [hLa, hLb]
    push_cast
    ring
  -- the four sums
  have hinj : Set.InjOn (a3y_ptOr X T) s' := by
    intro u hu u' hu' he
    rw [hpt u (hs'mem u hu).2.2, hpt u' (hs'mem u' hu').2.2] at he
    exact a3y_pt_injective T u u' _ _ he
  have S3 : ∑ u ∈ s, c u * a3i_intersectPrime X.left u v T =
      ∑ u ∈ s', c u * (a3i_serreMult X.left T u v : ℚ) := by
    rw [hs'def, Finset.sum_filter]
    refine Finset.sum_congr rfl fun u _ => ?_
    split_ifs with hp
    · obtain ⟨hcu, huT⟩ := hp
      obtain ⟨D, -, -, hcohu, -⟩ := hcoh u hcu
      rw [a3z_intersectPrime_apply_of_proper X.left u v T (hD u hcu) huT hvT
        (by rw [hT, hcohu, add_right_comm])]
    · by_cases hcu : c u = 0
      · rw [hcu, zero_mul]
      · have huT : ¬ u ⤳ T := fun h => hp ⟨hcu, h⟩
        have : a3i_intersectPrime X.left u v T = 0 := by
          by_contra hne
          exact huT (a3y_comps_spec u v (a3z_intersectPrime_ne_zero X.left u v T hne)).1
        rw [this, mul_zero]
  have S4 : ∑ u ∈ s', c u * (a3i_serreMult X.left T u v : ℚ) =
      ∑ 𝔇 ∈ G, c (X.left.fromSpecStalk T 𝔇) *
        (a3i_serreMult X.left T (X.left.fromSpecStalk T 𝔇) v : ℚ) := by
    rw [← Finset.sum_subset (s₁ := s'.image (a3y_ptOr X T)) Finset.subset_union_right,
      Finset.sum_image hinj]
    · refine Finset.sum_congr rfl fun u hu => ?_
      rw [hpt u (hs'mem u hu).2.2, a3y_fromSpecStalk_pt]
    · intro 𝔇 _ hn
      have : c (X.left.fromSpecStalk T 𝔇) = 0 := by
        by_contra hcu
        apply hn
        refine Finset.mem_image.2 ⟨X.left.fromSpecStalk T 𝔇, ?_, ?_⟩
        · rw [hs'def, Finset.mem_filter]
          refine ⟨?_, hcu, a3y_specializes_fromSpecStalk T 𝔇⟩
          by_contra hns
          exact hcu (hs _ hns)
        · rw [hpt _ (a3y_specializes_fromSpecStalk T 𝔇), a3y_pt_fromSpecStalk]
      rw [this, zero_mul]
  have hvanA : ∀ 𝔇 ∈ G, 𝔇 ∉ Fa → La 𝔇 = 0 := by
    intro 𝔇 hG hn
    have h𝔇 : a ∉ 𝔇.asIdeal := fun ha𝔇 =>
      hn ((hFa 𝔇).2 ⟨(hGprop 𝔇 hG).1, ha𝔇, (hGprop 𝔇 hG).2⟩)
    simp only [hLa]
    rw [a3e_locLen_eq_zero 𝔇 _ a h𝔇 (a3z_smul_quotSMulTop a _)]
    rfl
  have hvanB : ∀ 𝔇 ∈ G, 𝔇 ∉ Fb → Lb 𝔇 = 0 := by
    intro 𝔇 hG hn
    have h𝔇 : b ∉ 𝔇.asIdeal := fun hb𝔇 =>
      hn ((hFb 𝔇).2 ⟨(hGprop 𝔇 hG).1, hb𝔇, (hGprop 𝔇 hG).2⟩)
    simp only [hLb]
    rw [a3e_locLen_eq_zero 𝔇 _ b h𝔇 (a3z_smul_quotSMulTop b _)]
    rfl
  have S1 : ∑ 𝔇 ∈ Fa, La 𝔇 * χ 𝔇 = ∑ 𝔇 ∈ G, La 𝔇 * χ 𝔇 :=
    Finset.sum_subset (fun 𝔇 h => Finset.mem_union_left _ (Finset.mem_union_left _ h))
      fun 𝔇 hG hn => by rw [hvanA 𝔇 hG hn, zero_mul]
  have S2 : ∑ 𝔇 ∈ Fb, Lb 𝔇 * χ 𝔇 = ∑ 𝔇 ∈ G, Lb 𝔇 * χ 𝔇 :=
    Finset.sum_subset (fun 𝔇 h => Finset.mem_union_left _ (Finset.mem_union_right _ h))
      fun 𝔇 hG hn => by rw [hvanB 𝔇 hG hn, zero_mul]
  have keya' : ∑ 𝔇 ∈ Fa, La 𝔇 * χ 𝔇 = ∑ z ∈ a3y_compsAt X w v T,
      (a3i_serreMult X.left z w v : ℤ) * a3e_herbrand a (A ⧸ a3i_stalkIdeal X.left T z) := keya
  have keyb' : ∑ 𝔇 ∈ Fb, Lb 𝔇 * χ 𝔇 = ∑ z ∈ a3y_compsAt X w v T,
      (a3i_serreMult X.left z w v : ℤ) * a3e_herbrand b (A ⧸ a3i_stalkIdeal X.left T z) := keyb
  rw [S3, S4, ← Finset.sum_congr rfl hterm]
  have : ∑ 𝔇 ∈ G, ((La 𝔇 - Lb 𝔇) * χ 𝔇) =
      ∑ z ∈ a3y_compsAt X w v T, (a3i_serreMult X.left z w v : ℤ) *
        (a3e_herbrand a (A ⧸ a3i_stalkIdeal X.left T z) -
          a3e_herbrand b (A ⧸ a3i_stalkIdeal X.left T z)) := by
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
    rw [← S1, ← S2, keya', keyb']
  rw [← Int.cast_sum, this]
  push_cast
  rfl

end point


section sumMem
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [LocallyOfFiniteType X.hom]
  [IsNoetherian X.left]

/-- A rational combination of principal divisors of nonzero rational functions on subvarieties is
rationally equivalent to zero.
Source: Fulton, *Intersection Theory*, second edition, §1.3 (definition of `Rat_k X`). -/
theorem a3z_sum_principal_mem (S : Finset X.left) (r : X.left → ℚ)
    (ψ : (z : X.left) → (cycleComponent X.left z).functionField) (hψ : ∀ z ∈ S, ψ z ≠ 0) :
    ∑ z ∈ S, (a2_principalCycle X.left ℚ z (ψ z)).mapRange (r z * ·) (mul_zero _) ∈
      a3i_ratAll X.left := by
  refine AddSubgroup.sum_mem _ fun z hz => ?_
  obtain ⟨-, n, hn, -⟩ := a1d_height_eq_trdeg (X := X) z
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · -- a point carries no divisor
    have h0 : a2_principalCycle X.left ℚ z (ψ z) = 0 := by
      ext x
      by_contra hx
      obtain ⟨D, hD, hD1, -⟩ := a3z_principalCycle_ne_zero X.left z (ψ z) (hψ z hz) x hx
      have hzx : z ⤳ x := hD ▸ a3z_specializes_pt z D
      have hcoh : coheight x = coheight z + 1 := by
        rw [← hD]
        exact (a3y_coheight_eq_one_iff X z D).1 hD1
      have hne : z ≠ x := by
        rintro rfl
        have : IsLocallyNoetherian X.left := inferInstance
        obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.1 (a3c_coheight_ne_top X.left z)
        rw [← hc] at hcoh
        norm_cast at hcoh
        omega
      have hlt : x < z := lt_of_le_not_ge (Scheme.le_iff_specializes.2 hzx)
        fun h' => hne (hzx.antisymm (Scheme.le_iff_specializes.1 h')).eq
      have := Order.height_strictMono hlt
        (lt_of_le_of_lt (Order.height_mono hlt.le) (by rw [hn]; exact WithTop.coe_lt_top 0))
      rw [hn] at this
      exact absurd this (by simp)
    rw [h0]
    convert (a3i_ratAll X.left).zero_mem
    ext x
    simp
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact (le_iSup (fun k : ℕ => a2_ratEquivDim X.left ℚ k) k)
      (AddSubgroup.subset_closure ⟨z, ψ z, _, hn, hψ z hz, rfl⟩)

end sumMem

section cycle
variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsNoetherian X.left]
  (w v : X.left) (hWV : a3i_MeetProperly X.left w v)

open Classical in
include hWV in
/-- The cycle form of Fulton, Theorem 2.4, for Serre's product on a smooth complex variety. Let
`W = closure {w}` and `V = closure {v}` meet properly, and let `φ ≠ 0` be a rational function on
`W` whose divisor meets `V` properly and which is a unit at every component `Z` of `W ∩ V`, with
restriction `ψ_Z = φ|_Z`. Then `[div φ] · [V] = Σ_Z i(Z; W · V) [div ψ_Z]`.
Source: Fulton, *Intersection Theory*, second edition, Theorem 2.4 and §2.3; Serre, *Algèbre
locale, multiplicités*, Chapitre V, C. -/
theorem a3z_principal_intersect (φ : (cycleComponent X.left w).functionField) (hφ : φ ≠ 0)
    (hD : ∀ d, a2_principalCycle X.left ℚ w φ d ≠ 0 → a3i_MeetProperly X.left d v)
    (ψ : (z : X.left) → (cycleComponent X.left z).functionField)
    (hψ : ∀ z ∈ a3y_comps w v, a3z_IsRestriction w φ z (ψ z)) :
    a3i_intersect X.left (a2_principalCycle X.left ℚ w φ)
        (Function.locallyFinsuppWithin.single v 1) =
      ∑ z ∈ (a3y_comps_finite w v).toFinset, (a2_principalCycle X.left ℚ z (ψ z)).mapRange
        ((a3i_serreMult X.left z w v : ℚ) * ·) (mul_zero _) := by
  classical
  set c := a2_principalCycle X.left ℚ w φ with hc
  set s := (a3c_support_finite c).toFinset
  have hs : ∀ u ∉ s, c u = 0 := fun u hu => by simpa [s] using hu
  ext T
  rw [a3z_intersect_single_apply X.left c v s hs T, Function.locallyFinsuppWithin.coe_sum,
    Finset.sum_apply]
  simp only [Function.locallyFinsuppWithin.mapRange_apply]
  by_cases hP : w ⤳ T ∧ v ⤳ T ∧ coheight T = coheight w + coheight v + 1
  · obtain ⟨hwT, hvT, hT⟩ := hP
    rw [a3z_principal_point X w v T hwT hvT (fun z hz _ => a3y_coheight_comps w v hWV hz) hT φ hφ
      hD ψ hψ s hs]
    simp only [a3y_compsAt]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun z _ => ?_
    split_ifs with hzT
    · rfl
    · rw [a3y_principalCycle_apply_of_not_mem X.left z (ψ z) T, mul_zero]
      rintro ⟨TZ, rfl⟩
      exact hzT (a3z_specializes_pt z TZ)
  · have hL : ∀ u ∈ s, c u * a3i_intersectPrime X.left u v T = 0 := by
      intro u _
      by_cases hcu : c u = 0
      · rw [hcu, zero_mul]
      by_cases hi : a3i_intersectPrime X.left u v T = 0
      · rw [hi, mul_zero]
      exfalso
      obtain ⟨D, hD', hD1, -⟩ := a3z_principalCycle_ne_zero X.left w φ hφ u hcu
      have hcohu : coheight u = coheight w + 1 := by
        rw [← hD']
        exact (a3y_coheight_eq_one_iff X w D).1 hD1
      have hwu : w ⤳ u := hD' ▸ a3z_specializes_pt w D
      have hTc := a3z_intersectPrime_ne_zero X.left u v T hi
      obtain ⟨huT, hvT, -⟩ := a3y_comps_spec u v hTc
      refine hP ⟨hwu.trans huT, hvT, ?_⟩
      rw [a3y_coheight_comps u v (hD u hcu) hTc, hcohu, add_right_comm]
    have hR : ∀ z ∈ (a3y_comps_finite w v).toFinset,
        (a3i_serreMult X.left z w v : ℚ) * a2_principalCycle X.left ℚ z (ψ z) T = 0 := by
      intro z hz
      rw [Set.Finite.mem_toFinset] at hz
      by_cases h0 : a2_principalCycle X.left ℚ z (ψ z) T = 0
      · rw [h0, mul_zero]
      exfalso
      have hψ0 : ψ z ≠ 0 := a3z_isRestriction_ne_zero w (hψ z hz)
      obtain ⟨TZ, hTZ, hTZ1, -⟩ := a3z_principalCycle_ne_zero X.left z (ψ z) hψ0 T h0
      have hzT : z ⤳ T := hTZ ▸ a3z_specializes_pt z TZ
      obtain ⟨hwz, hvz, -⟩ := a3y_comps_spec w v hz
      refine hP ⟨hwz.trans hzT, hvz.trans hzT, ?_⟩
      rw [← hTZ, (a3y_coheight_eq_one_iff X z TZ).1 hTZ1, a3y_coheight_comps w v hWV hz]
    rw [Finset.sum_eq_zero hL, Finset.sum_eq_zero hR]

open Classical in
include hWV in
/-- Under the hypotheses of `a3z_principal_intersect`, `[div φ] · [V]` is rationally equivalent to
zero. -/
theorem a3z_principal_intersect_mem (φ : (cycleComponent X.left w).functionField) (hφ : φ ≠ 0)
    (hD : ∀ d, a2_principalCycle X.left ℚ w φ d ≠ 0 → a3i_MeetProperly X.left d v)
    (hunit : ∀ z ∈ a3y_comps w v, a3z_UnitAt w φ z) :
    a3i_intersect X.left (a2_principalCycle X.left ℚ w φ)
      (Function.locallyFinsuppWithin.single v 1) ∈ a3i_ratAll X.left := by
  classical
  have hex : ∀ z, ∃ ψ : (cycleComponent X.left z).functionField,
      z ∈ a3y_comps w v → ψ ≠ 0 ∧ a3z_IsRestriction w φ z ψ := by
    intro z
    by_cases hz : z ∈ a3y_comps w v
    · obtain ⟨ψ, h1, h2⟩ := a3z_exists_restriction w (hunit z hz)
      exact ⟨ψ, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose ψ hψ using hex
  rw [a3z_principal_intersect X w v hWV φ hφ hD ψ fun z hz => (hψ z hz).2]
  exact a3z_sum_principal_mem X _ _ ψ fun z hz => (hψ z (by simpa using hz)).1

end cycle

end HodgeLean.Adapters
