{-# OPTIONS --cubical-compatible --safe #-}
module two_four where

open import Data.Nat 
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (Bool; true; false; _∨_; _&&_)

-- open import logic

-- data _<=_ : ℕ → ℕ → Set where
--  z<=n : {x : ℕ} → zero <= x
--  s<=s : {x y : ℕ} → x <= y → suc x <= suc y

-- hint : it has two inputs, use recursion
nat-<> : { x y : ℕ } → x < y → y < x → ⊥
nat-<>   (s≤s x<y) (s≤s y<x) = nat-<> x<y y<x

-- hint : use recursion
nat-<≡ : { x : ℕ } → x < x → ⊥
nat-<≡ (s≤s x<x) = nat-<≡ x<x

-- hint : use refl and recursion
nat-≡< : {x y : ℕ} → x ≡ y → x < y → ⊥
nat-≡< refl (s≤s x<y) = nat-≡< refl x<y

¬a≤a : {la : ℕ} → suc la ≤ la → ⊥
¬a≤a (s≤s lt) = ¬a≤a lt

-- hint : make case with la first
a<sa : {i : ℕ} → i < suc i 
a<sa {zero} = s≤s z≤n
a<sa {suc i} =  s≤s a<sa 

-- hint  : ¬ has an input, use recursion
=→¬< : {x : ℕ  } → ¬ ( x < x )
=→¬< = {!!}

-- hint : two inputs, try nat-<>
>→¬< : {x y : ℕ  } → (x < y ) → ¬ ( y < x )
>→¬< = {!!}

-- hint : make cases on all arguments. return case1 or case2
-- hint : use with on suc case
<-∨ : { x y : ℕ } → x < suc y → ( (x nat-<≡ y ) ∨ (x < y) )
<-∨ = {!!}

max : (x y : ℕ) → ℕ
max = {!!}

sum :  (x y : ℕ) → ℕ
sum zero y = y
sum (suc x) y = suc ( sum x y )

sum' :  (x y : ℕ) → ℕ
sum' x zero = x
sum' x (suc y) = suc (sum' x y)

sum-sym0 :  {x y : ℕ} → sum x y ≡ sum' y x
sum-sym0 {zero} {zero} = refl
sum-sym0 {suc x} {y} = cong (λ k → suc k ) (sum-sym0 {x} {y})
sum-sym0 {zero} {y}  = refl

sum-6 : sum 3 4 ≡ 7
sum-6 = refl

sum1 : (x y : ℕ) → sum x (suc y)  ≡ suc (sum x y )
sum1 x y = let open ≡-Reasoning in 
   begin 
       sum x (suc y)
   ≡⟨ {!!} ⟩
       suc (sum x y )
   ∎

sum0 : (x : ℕ) → sum 0 x  ≡ x
sum0 zero = refl
sum0 (suc x) = refl 

sum-sym : (x y : ℕ) → sum x y  ≡ sum y x
sum-sym = {!!}

sum-assoc : (x y z : ℕ) → sum x (sum y z ) ≡ sum (sum x y)  z 
sum-assoc = {!!}

mul :  (x y : ℕ) → ℕ
mul x zero = zero
mul x (suc y) = sum x ( mul x y )

mulr :  (x y : ℕ) → ℕ
mulr zero y = zero
mulr (suc x) y = sum y ( mulr x y )

mul-sym1 : {x y : ℕ } → mul x y ≡ mulr y x
mul-sym1 {zero} {zero} = refl
mul-sym1 {zero} {suc y} = begin
     mul zero (suc y)
   ≡⟨⟩
     sum 0 (mul 0 y)
   ≡⟨ cong (λ k → sum 0 k ) {!!}  ⟩
      sum 0 (mulr y 0)
   ≡⟨⟩
     mulr (suc y) zero
   ∎ where open ≡-Reasoning 
mul-sym1 {suc x} {y} = {!!}

mul-9 : mul 3 4 ≡ 12
mul-9 = {!!}

mul-distr1 : (x y : ℕ) → mul x (suc y) ≡ sum x ( mul x y )
mul-distr1 = {!!}

mul-sym0 : (x : ℕ) → mul zero x  ≡ mul x zero 
mul-sym0 = {!!}

mul-sym : (x y : ℕ) → mul x y  ≡ mul y x
mul-sym = {!!}

mul-distr : (y z w : ℕ) → sum (mul y z) ( mul w z ) ≡ mul (sum y w)  z
mul-distr = {!!}

mul-assoc : (x y z : ℕ) → mul x (mul y z ) ≡ mul (mul x y)  z 
mul-assoc = {!!}

evenp : (x : ℕ) → Bool
evenp = {!!}
