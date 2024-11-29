module two_eight where
                                                                        
postulate A : Set

postulate a : A
postulate b : A
postulate c : A


infixr 40 _::_
data  List  (A : Set ) : Set  where
   [] : List A
   _::_ : A →  List A → List A 

--
--                           A      List A
--     -------------- []    ---------------- _::_
--         List A               List A
--

infixl 30 _++_
_++_ :   {A : Set } → List A → List A → List A
[] ++ y = y
(x :: x₁) ++ y = x :: (x₁ ++ y )

l1 = a :: []
l2 = a :: b  :: a :: c ::  []

l3 = l1 ++ l2

data Node  ( A : Set  ) : Set  where
   leaf  : A → Node A
   node  : Node A → Node A → Node A

flatten :  { A : Set } → Node A → List A
flatten ( leaf a )   = a :: []
flatten ( node a b ) = flatten a ++ flatten b

n1 = node ( leaf a ) ( node ( leaf b ) ( leaf c ))

open  import  Relation.Binary.PropositionalEquality

++-assoc :  (L : Set ) ( xs ys zs : List L ) → (xs ++ ys) ++ zs  ≡ xs ++ (ys ++ zs)
++-assoc A [] ys zs = let open ≡-Reasoning in
  begin -- to prove ([] ++ ys) ++ zs  ≡ [] ++ (ys ++ zs)
   ( [] ++ ys ) ++ zs
  ≡⟨ refl ⟩
    ys ++ zs
  ≡⟨⟩
    [] ++ ( ys ++ zs )
  ∎
  
++-assoc A (x :: xs) ys zs = let open  ≡-Reasoning in
  begin -- to prove ((x :: xs) ++ ys) ++ zs == (x :: xs) ++ (ys ++ zs)
    ((x :: xs) ++ ys) ++ zs
  ≡⟨ refl ⟩
     (x :: (xs ++ ys)) ++ zs
  ≡⟨ refl ⟩
    x :: ((xs ++ ys) ++ zs)
  ≡⟨ cong (_::_ x) (++-assoc A xs ys zs) ⟩ 
    x :: (xs ++ (ys ++ zs))
  ≡⟨ refl ⟩
    (x :: xs) ++ (ys ++ zs)
  ∎

-- open import Data.Nat

data Nat : Set where
  zero : Nat 
  suc  : Nat → Nat

_+_ : Nat → Nat → Nat
zero + y = y
suc x + y = suc (x + y)

sym1 : {A : Set} → {a b : A} → a ≡ b → b ≡ a
sym1 {_} {a} {.a} refl = refl

trans1 : {A : Set} → {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans1 {_} {a} {b} {.a} refl refl = refl

cong1 : {A B : Set} → {a b : A} → (f : A → B) → a ≡ b → f a ≡ f b 
cong1 f refl = refl

induction : (P : (x : Nat) → Set) → (initial : P zero ) → (induction-setp : ((x : Nat) → P x → P (suc x))) → (x : Nat) → P x
induction P initial induction-setp zero = initial
induction P initial induction-setp (suc x) =  induction-setp x ( induction P initial induction-setp x)

induction' : (P : (x : Nat) → Set) → (initial : P zero ) → (induction-setp : ((x : Nat) → P x → P (suc x))) → (x : Nat) → P x
induction' P initial induction-setp x = {!!} where
    ind1 : {!!} → P x
    ind1 = {!!}

+-comm : {x y : Nat} → x + y ≡ y + x
+-comm {zero} {y} = sym1 lemma01  where
   lemma01 : {y : Nat} → y + zero ≡ y
   lemma01 {zero} = refl                               --      (zero + zero ) → zero → zero + zero ≡ zero
   lemma01 {suc y} = cong1 (λ x → suc x) (lemma01 {y}) ---  (suc y + zero) ≡ suc y
                               --   suc (y + zero) ≡ suc y  ← y + zero ≡ y 
+-comm {suc x} {y} = {!!}

_*_ : Nat → Nat → Nat
zero * y = zero
suc x * y = y + (x * y)

--
--     * * *    * *
--     * * *  ≡ * *
--              * *

*-comm : {x y : Nat} → x * y ≡ y * x
*-comm = {!!}

length : {L : Set} → List L →  Nat
length [] = zero
length (_ :: T ) = suc ( length T )

lemma : {L : Set} → (x y : List L ) → ( length x + length y ) ≡ length ( x ++ y )
lemma [] [] = refl
lemma [] (_ :: _) = refl
lemma (H :: T) L =  let open  ≡-Reasoning in
  begin 
     {!!}
  ≡⟨ {!!} ⟩
     {!!}
  ∎

