import HodgeLean.Foundations.AnalyticDivisorAlgebraic11
import Mathlib.Analysis.Analytic.Uniqueness

noncomputable section
open Filter Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
namespace HodgeLean.Foundations.Program

def b54_entireRing (n : ℕ) : Subring ((Fin n → ℂ) → ℂ) where
  carrier := {f | ∀ z, AnalyticAt ℂ f z}
  zero_mem' := fun _ => analyticAt_const
  one_mem' := fun _ => analyticAt_const
  add_mem' hf hg := fun z => (hf z).add (hg z)
  neg_mem' hf := fun z => (hf z).neg
  mul_mem' hf hg := fun z => (hf z).mul (hg z)

def b54_entireGerm (n : ℕ) (p : Fin n → ℂ) : b54_entireRing n →+* AnalyticGerm n where
  toFun f := ⟨Filter.Germ.ofFun (fun z => f.val (p + z)),
    ⟨fun z => f.val (p + z),
      ((f.property (p + 0)).comp (analyticAt_const.add analyticAt_id)), rfl⟩⟩
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

theorem b54_entireGerm_injective (n : ℕ) (p : Fin n → ℂ) :
    Function.Injective (b54_entireGerm n p) := by
  intro f g h
  have he : (fun z => f.val (p + z)) =ᶠ[𝓝 0] (fun z => g.val (p + z)) :=
    Filter.Germ.coe_eq.mp (by exact congrArg Subtype.val h)
  have hh : (fun z => f.val (p + z)) = (fun z => g.val (p + z)) :=
    AnalyticOnNhd.eq_of_eventuallyEq
      (fun z _ => (f.property (p + z)).comp (analyticAt_const.add analyticAt_id))
      (fun z _ => (g.property (p + z)).comp (analyticAt_const.add analyticAt_id)) he
  apply Subtype.ext
  funext z
  simpa using congrFun hh (z - p)

def b54_entireGermAt (n : ℕ) (p : Fin n → ℂ) : b54_entireRing n →+* AnalyticGermAt n p where
  toFun f := ⟨Filter.Germ.ofFun f.val, ⟨f.val, f.property p, rfl⟩⟩
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

theorem b54_entireGermAt_injective (n : ℕ) (p : Fin n → ℂ) :
    Function.Injective (b54_entireGermAt n p) := by
  intro f g h
  apply Subtype.ext
  exact AnalyticOnNhd.eq_of_eventuallyEq (fun z _ => f.property z)
    (fun z _ => g.property z) (Filter.Germ.coe_eq.mp (congrArg Subtype.val h))

theorem b54_analyticGermAt_isDomain (n : ℕ) (p : Fin n → ℂ) :
    IsDomain (AnalyticGermAt n p) := by
  letI := spec_analyticGerm_ufd n
  letI : IsDomain (AnalyticGerm n) := {}
  obtain ⟨e, _⟩ := spec_germ_translation_equiv n p
  exact Function.Injective.isDomain e.toRingHom e.injective

theorem b54_analyticGermAt_integrallyClosed (n : ℕ) (p : Fin n → ℂ) :
    IsIntegrallyClosed (AnalyticGermAt n p) := by
  letI := spec_analyticGerm_ufd n
  letI : IsDomain (AnalyticGerm n) := {}
  obtain ⟨e, _⟩ := spec_germ_translation_equiv n p
  exact IsIntegrallyClosed.of_equiv e.symm

set_option backward.isDefEq.respectTransparency false in
theorem b54_entire_dvd_of_germ_dvd (n : ℕ) (a b : b54_entireRing n) (hb : b ≠ 0)
    (hdiv : ∀ p, b54_entireGermAt n p b ∣ b54_entireGermAt n p a) : b ∣ a := by
  choose h hh using hdiv
  choose H hH he using (fun p => (h p).property)
  have heq (p : Fin n → ℂ) : a.val =ᶠ[𝓝 p] (fun z => b.val z * H p z) := by
    apply Filter.Germ.coe_eq.mp
    have hh' := congrArg Subtype.val (hh p)
    change Filter.Germ.ofFun a.val = Filter.Germ.ofFun b.val * (h p).val at hh'
    rw [← he p] at hh'
    exact hh'
  let g : (Fin n → ℂ) → ℂ := fun p => H p p
  have hlocal (p : Fin n → ℂ) : g =ᶠ[𝓝 p] H p := by
    filter_upwards [(heq p).eventually_nhds, (hH p).eventually_analyticAt] with q hq hA
    let y : AnalyticGermAt n q := ⟨Filter.Germ.ofFun (H p), ⟨H p, hA, rfl⟩⟩
    have hprod : b54_entireGermAt n q a = b54_entireGermAt n q b * y := by
      apply Subtype.ext
      exact Filter.Germ.coe_eq.mpr hq
    letI := b54_analyticGermAt_isDomain n q
    have hbn : b54_entireGermAt n q b ≠ 0 :=
      (map_ne_zero_iff _ (b54_entireGermAt_injective n q)).mpr hb
    have hhy : h q = y := mul_left_cancel₀ hbn ((hh q).symm.trans hprod)
    have hv := congrArg (analyticGermAtValue n q) hhy
    change (h q).val.value = H p q at hv
    rw [← he q] at hv
    exact hv
  refine ⟨⟨g, fun p => (hH p).congr (hlocal p).symm⟩, ?_⟩
  apply Subtype.ext
  funext p
  exact (heq p).self_of_nhds

theorem b54_entire_isDomain (n : ℕ) : IsDomain (b54_entireRing n) := by
  letI := b54_analyticGermAt_isDomain n 0
  exact Function.Injective.isDomain (b54_entireGermAt n 0) (b54_entireGermAt_injective n 0)

set_option backward.isDefEq.respectTransparency false in
theorem b54_entire_integrallyClosed (n : ℕ) : IsIntegrallyClosed (b54_entireRing n) := by
  let R := b54_entireRing n
  letI := b54_entire_isDomain n
  apply (isIntegrallyClosed_iff (FractionRing R)).mpr
  intro x hx
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R x
  have hb : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hd : b ∣ a := by
    apply b54_entire_dvd_of_germ_dvd n a b hb
    intro p
    let S := AnalyticGermAt n p
    letI := b54_analyticGermAt_isDomain n p
    letI := b54_analyticGermAt_integrallyClosed n p
    let f := b54_entireGermAt n p
    let φ : FractionRing R →+* FractionRing S :=
      IsFractionRing.map (b54_entireGermAt_injective n p)
    have hc : (algebraMap S (FractionRing S)).comp f =
        φ.comp (algebraMap R (FractionRing R)) := by
      ext r
      simp [φ, IsFractionRing.map, IsLocalization.map_eq, f, S]
    have hi := IsIntegral.map_of_comp_eq f φ hc hx
    obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff (FractionRing S)).mp
      (b54_analyticGermAt_integrallyClosed n p) hi
    have hfmap (r : R) : φ (algebraMap R (FractionRing R) r) =
        algebraMap S (FractionRing S) (f r) := (RingHom.congr_fun hc r).symm
    simp only [map_div₀, hfmap] at hy
    have hfb : algebraMap S (FractionRing S) (f b) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective S (FractionRing S))).mpr
        ((map_ne_zero_iff _ (b54_entireGermAt_injective n p)).mpr hb)
    rw [eq_div_iff hfb] at hy
    refine ⟨y, ?_⟩
    apply IsFractionRing.injective S (FractionRing S)
    rw [map_mul, mul_comm]
    exact hy.symm
  obtain ⟨y, hy⟩ := hd
  refine ⟨y, ?_⟩
  rw [hy, map_mul, mul_div_cancel_left₀]
  exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).mpr hb

def b54_entireTranslate (n : ℕ) (p : Fin n → ℂ) : b54_entireRing n →+* b54_entireRing n where
  toFun f := ⟨fun z => f.val (p + z),
    fun z => (f.property (p + z)).comp (analyticAt_const.add analyticAt_id)⟩
  map_one' := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

theorem b54_entireTranslate_injective (n : ℕ) (p : Fin n → ℂ) :
    Function.Injective (b54_entireTranslate n p) := by
  intro f g h
  apply Subtype.ext
  funext z
  have hh := congrFun (congrArg Subtype.val h) (z - p)
  simpa [b54_entireTranslate] using hh

end HodgeLean.Foundations.Program
