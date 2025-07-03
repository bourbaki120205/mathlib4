import Mathlib
open Ideal Padic Nat
open scoped algebraMap

theorem pow_eq_ex_eq {L : Type*} [Field L] (ζ : L) (n : ℕ) [NeZero n] (hζ : IsPrimitiveRoot ζ n)
    {a b : ZMod n} : ζ ^ a.val = ζ ^ b.val ↔ a = b := by
  constructor
  · rintro h
    have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne n)
    have h1:ζ^((b.val:ℤ)-(a.val:ℤ))=1 := by
      rw [zpow_sub₀ hζ0]
      rw [div_eq_one_iff_eq (zpow_ne_zero _ hζ0)]
      simp only [zpow_natCast, h]
    have h3: (n:Int) ∣ ((b.val:ℤ) - (a.val:ℤ)) := by
      rwa [hζ.zpow_eq_one_iff_dvd] at h1
    have mod_eq: a.val ≡ b.val [MOD n]:= by
      rw[modEq_iff_dvd]
      exact h3
    rwa [← ZMod.eq_iff_modEq_nat, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at mod_eq
  · rintro rfl
    rfl

variable
    -- let K be a number field with ring of integers A
    {A K : Type*}
    [CommRing A] [IsDedekindDomain A]
    [Field K] [NumberField K] [Algebra A K]
    [IsFractionRing A K]
    [IsIntegralClosure A ℤ K]
    -- let L be an algebraic closure of K
    {L : Type*} [Field L] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L]
    [IsAlgClosure K L]
    -- and let B be the integral closure of A in L
    {B : Type*} [CommRing B] [Algebra B L]
    [Algebra A B] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    -- Let G be the Galois group of L/K
    variable {G : Type*} [Group G]
    [MulSemiringAction G L]
    [SMulCommClass G K L]
    [Algebra.IsInvariant K L G]
    [MulSemiringAction G B]
    [SMulCommClass G A B]
    [Algebra.IsInvariant A B G]
    [IsScalarTower G B L]
    -- Let F be an element of G
    (F : G)
    -- Let I be a maximal ideal of B
    (I : Ideal B) (hI : I.IsMaximal)
    -- assume F is a Frobenius element at I
    (hF : IsArithFrobAt A F I)
    -- Then for a prime ell not in I...
    (l : ℕ) [Fact (Nat.Prime l)](hlp : ↑l ∉ I)





-- the value of the cyclotomic character at Frob_I is #A/PA where P = I ∩ A
include hI hF hlp
theorem cyclo_thing :
    ((cyclotomicCharacter L l (MulSemiringAction.toRingEquiv G L F)) : ℤ_[l]) =
      Nat.card (A ⧸ I.under A) := by
      set q:= ↑(Nat.card (A ⧸ under A I))
      set g:= (MulSemiringAction.toRingEquiv G L F)


      --∀i:ℕ , ↑(l^i) ∉ I
      have primeI: I.IsPrime := hI.isPrime
      have H: ∀i:ℕ , ↑(l^i) ∉ I := by
        by_contra hi
        simp at hi
        rw[← mem_radical_iff,IsPrime.radical primeI] at hi
        exact hlp hi

      --B in an integral domain, should be tautology
      have DomainB: IsDomain B:= by
        sorry

      --reduce modular l^i
      rw[← PadicInt.ext_of_toZModPow]
      intro i
      simp
      specialize H i

      --have enough roots in B
      have ineed : ∀ (i : ℕ), HasEnoughRootsOfUnity L (l ^ i):=sorry
      have ext_root : ∀ (i : ℕ), ∃ ζ : B,IsPrimitiveRoot ζ (l ^ i):= by
        sorry
      obtain ⟨ζ,hζ⟩ := ext_root i
      have hζ' : (ζ : L) ^ (l ^ i) = 1 := sorry

      --real proof starts here
      have good_Andrew : g ζ = (ζ ^ q : B) := by
        have Andrew_Theorem:= AlgHom.IsArithFrobAt.apply_of_pow_eq_one hF hζ.pow_eq_one H
        have tauto: (F • ζ : B) = g ζ := algebraMap.coe_smul G B L F ζ
        rw [←tauto, ←Andrew_Theorem]
        rfl

      have ccspec:= cyclotomicCharacter.spec l g ↑ζ hζ'
      have iwant: (ζ:L)^q = ζ^( (cyclotomicCharacter L l g).val.toZModPow i).val := by
        rw[← ccspec,good_Andrew]
        exact Eq.symm (algebraMap.coe_pow ζ q)







      have amzing :(PadicInt.toZModPow i) ↑((cyclotomicCharacter L l) g) =
       ((cyclotomicCharacter L l g).val.toZModPow i) := rfl






      sorry



#check AlgHom.IsArithFrobAt.apply_of_pow_eq_one
/-have HH: algebraMap B L ((MulSemiringAction.toAlgHom A B F) ζ )= g (algebraMap B L ζ) :=sorry-/
