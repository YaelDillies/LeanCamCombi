import Mathlib.Data.Nat.Squarefree
import LeanCamCombi.Mathlib.Data.Nat.Factorization.Basic
import LeanCamCombi.Mathlib.Data.Nat.Order.Lemmas

open Finset
open scoped BigOperators

namespace Nat
variable {m n p : ℕ} {s : Finset ℕ}

alias _root_.Squarefree.natFactorization_le_one := Squarefree.factorization_le_one

lemma coprime_div_gcd_of_squarefree (hm : Squarefree m) (hn : n ≠ 0) : Coprime (m / gcd m n) n := by
  have : Coprime (m / gcd m n) (gcd m n) :=
    coprime_of_squarefree_mul $ by simpa [Nat.div_mul_cancel, gcd_dvd_left]
  simpa [Nat.div_mul_cancel, gcd_dvd_right] using
    (coprime_div_gcd_div_gcd (m := m) (gcd_ne_zero_right hn).bot_lt).mul_right this

lemma factorization_eq_one_of_squarefree (hn : Squarefree n) (hp : p.Prime) (hpn : p ∣ n) :
    factorization n p = 1 :=
  (hn.natFactorization_le_one _).antisymm $ (hp.dvd_iff_one_le_factorization hn.ne_zero).1 hpn

lemma prod_primeFactors_of_squarefree (hn : Squarefree n) : ∏ p in n.primeFactors, p = n := by
  convert factorization_prod_pow_eq_self hn.ne_zero
  refine prod_congr rfl fun p hp ↦ ?_
  simp only [support_factorization, toFinset_factors, mem_primeFactors_of_ne_zero hn.ne_zero] at hp
  simp_rw [factorization_eq_one_of_squarefree hn hp.1 hp.2, pow_one]

lemma primeFactors_prod (hs : ∀ p ∈ s, p.Prime) : primeFactors (∏ p in s, p) = s := by
  have hn : ∏ p in s, p ≠ 0 := prod_ne_zero_iff.2 fun p hp ↦ (hs _ hp).ne_zero
  ext p
  rw [mem_primeFactors_of_ne_zero hn, and_congr_right (fun hp ↦ hp.prime.dvd_finset_prod_iff _)]
  refine' ⟨_, fun hp ↦ ⟨hs _ hp, _, hp, dvd_rfl⟩⟩
  rintro ⟨hp, q, hq, hpq⟩
  rwa [←((hs _ hq).dvd_iff_eq hp.ne_one).1 hpq]

lemma primeFactors_div_gcd (hm : Squarefree m) (hn  : n ≠ 0) :
    primeFactors (m / m.gcd n) = primeFactors m \ primeFactors n := by
  ext p
  have : m / m.gcd n ≠ 0 :=
    (Nat.div_ne_zero $ gcd_ne_zero_right hn).2 $ gcd_le_left _ hm.ne_zero.bot_lt
  simp only [mem_primeFactors, ne_eq, this, not_false_eq_true, and_true, not_and, mem_sdiff,
    hm.ne_zero, hn, dvd_div_iff (gcd_dvd_left _ _)]
  refine ⟨fun hp ↦ ⟨⟨hp.1, dvd_of_mul_left_dvd hp.2⟩, fun _ hpn ↦ hp.1.not_unit $ hm _ $
    (mul_dvd_mul_right (dvd_gcd (dvd_of_mul_left_dvd hp.2) hpn) _).trans hp.2⟩, fun hp ↦
      ⟨hp.1.1, Coprime.mul_dvd_of_dvd_of_dvd ?_ (gcd_dvd_left _ _) hp.1.2⟩⟩
  rw [coprime_comm, hp.1.1.coprime_iff_not_dvd]
  exact fun hpn ↦ hp.2 hp.1.1 $ hpn.trans $ gcd_dvd_right _ _

lemma prod_primeFactors_invOn_squarefree :
    Set.InvOn (fun n : ℕ ↦ (factorization n).support) (fun s ↦ ∏ p in s, p)
      {s | ∀ p ∈ s, p.Prime} {n | Squarefree n} :=
  ⟨fun _s ↦ primeFactors_prod, fun _n ↦ prod_primeFactors_of_squarefree⟩

end Nat
