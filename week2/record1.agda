module record1 where

record _∧_ (A B : Set) : Set where
  field
     π1 : A
     π2 : B

ex0 : {A B : Set} → A ∧ B →  A
ex0 =  _∧_.π1 

--        A ∧ B
--    -------------
--          A

ex1 : {A B : Set} → ( A ∧ B ) → A 
ex1 a∧b =  _∧_.π1 a∧b

--       (A ∧ B)
--    -------------
--          A

open _∧_

ex0' : {A B : Set} → A ∧ B →  A
ex0' = π1

ex1' : {A B : Set} → ( A ∧ B ) → A 
ex1' a∧b =  π1 a∧b

ex2 : {A B : Set} → ( A ∧ B ) → B 
ex2 a∧b = π2 a∧b

--       (A ∧ B)
--    -------------
--          B

ex3 : {A B : Set} → A → B → ( A ∧ B ) 
ex3 a b = record { π1 = a ; π2 = b }

--       (A ∧ B)
--    -------------
--       (A ∧ B)

ex4 : {A B : Set} → A → ( A ∧ A ) 
ex4 a  = record { π1 = a ;  π2 = a}

--          A 
--    -------------
--      ( A ∧ A )

ex5 : {A B C : Set} → ( A ∧ B ) ∧ C  →  A ∧ (B ∧ C) 
ex5 a∧b∧c = record { π1 = π1 ( π1 a∧b∧c ) ; π2 = record { π1 = π2 ( π1 a∧b∧c ) ; π2 = π2 a∧b∧c } }
-- パイ１は前者パイ２は後者

--    ( A ∧ B ) ∧ C 
--    -------------
--      A ∧ (B ∧ C) 

--
--                                 [(A → B ) ∧ ( B →  C) ]₁  
--                                ──────────────────────────────────── π1
--     [(A → B ) ∧ ( B →  C) ]₁        (A → B )    [A]₂
--   ──────────────────────────── π2 ─────────────────────── λ-elim
--          ( B →  C)                     B
--   ─────────────────────────────────────────── λ-elim
--                   C
--   ─────────────────────────────────────────── λ-intro₂
--                 A → C
--   ─────────────────────────────────────────── λ-intro₁
--     ( (A → B ) ∧ ( B →  C) )  → A → C

ex6 : {A B C : Set} → ( (A → B ) ∧ ( B → C) )  → A → C
ex6 x a =  ( π2 x )(( π1 x ) a )

ex6' : {A B C : Set} →  ( A → B ) → ( B → C ) → A → C
ex6' = λ a2b b2c a → b2c (a2b a)

-- A→A = λ ( x : A ) → x