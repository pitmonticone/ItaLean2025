import ItaLean.Damiano.ShadyAuxLemmas

/-
I was going to give a metaprogramming talk, but then I found a proof of Fermat's Last Theorem,
so I am going to talk about that instead!

Because the proof does not fit in this file, I added a `fermat` tactic in a previous file.
-/

theorem FLT {a b c n : Nat} (abc : a * b * c ≠ 0) (n3 : 3 ≤ n) :
    a ^ n + b ^ n ≠ c ^ n := by
  fermat

#print axioms FLT
#print FLT
