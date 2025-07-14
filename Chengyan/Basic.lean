import Mathlib
open Ideal Padic Nat
open scoped algebraMap


example {α β : Type} (f g : α → β) (x : α) (h : f = g) : f x = g x :=
  congr($h x)

lemma isDomain_of_faithfulSMul (B L : Type*) [CommRing B] [CommRing L] [IsDomain L]
    [Algebra B L] [FaithfulSMul B L] : IsDomain B :=
  Function.Injective.isDomain (algebraMap B L) <| by
  rwa [← faithfulSMul_iff_algebraMap_injective B L]

lemma faithfulSMul_of_isIntegralClosure (A B L : Type*) [CommRing A] [CommSemiring B] [CommRing L]
    [Algebra A L] [Algebra B L] [IsIntegralClosure B A L] : FaithfulSMul B L where
  eq_of_smul_eq_smul {b₁ b₂} h := by
    apply IsIntegralClosure.algebraMap_injective B A L
    simp [Algebra.algebraMap_eq_smul_one, h 1]

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
        have := faithfulSMul_of_isIntegralClosure A B L
        exact isDomain_of_faithfulSMul B L

      --reduce modular l^i
      rw[← PadicInt.ext_of_toZModPow]
      intro i
      simp
      specialize H i

      --have enough roots in B
      include K
      have ineed : ∀ (i : ℕ), HasEnoughRootsOfUnity L (l ^ i):=by
        intro i
        have aaa: L = (AlgebraicClosure K) := sorry
      sorry
