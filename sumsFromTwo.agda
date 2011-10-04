module sumsFromTwo where

-- Two element set with large elimination ---------------------------
data Two : Set where
  tt ff : Two 

if_then_else_ : {A : Two -> Set1} -> (x : Two) -> A tt -> A ff -> A x
if tt then a else b = a
if ff then a else b = b
---------------------------------------------------------------------

-- Set closed under Σ -----------------------------------------------
record Σ (A : Set) (B : A -> Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

split : {A : Set}{B : A -> Set} -> (C : Σ A B -> Set) ->
                        ((a : A) -> (b : B a) -> C (a , b)) ->
                        (x : Σ A B) -> C x
split C step (a , b) = step a b

fst : {A : Set}{B : A -> Set} -> Σ A B -> A
fst {A} {B} = split (λ _ → A) (λ a b → a)

snd : {A : Set}{B : A -> Set} -> (x : Σ A B) -> B (fst x)
snd {A} {B} = split (λ x → B (fst x)) (λ a b → b)
---------------------------------------------------------------------

-- Set1 closed under Σ ----------------------------------------------
record Σ1 (A : Set1) (B : A -> Set1) : Set1 where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

split1 : {A : Set1}{B : A -> Set1} -> (C : Σ1 A B -> Set1) ->
                        ((a : A) -> (b : B a) -> C (a , b)) ->
                        (x : Σ1 A B) -> C x
split1 C step (a , b) = step a b

---------------------------------------------------------------------

-- Set a subuniverse of Set1 ----------------------------------------
---- (emb and unemb should be the identity) -------------------------

data _↑ (A : Set) : Set1 where
  emb : A -> A ↑

unemb : {A : Set} -> A ↑ -> A
unemb (emb x) = x
---------------------------------------------------------------------

-- We get large elimination for Σ in Set for free -------------------
split01 : {A : Set}{B : A -> Set} -> (C : Σ A B -> Set1) ->
                        ((a : A) -> (b : B a) -> C (a , b)) ->
                        (x : Σ A B) -> C x
split01 {A} {B} C step x = split1 C↑ step↑ (embΣ x)
  where A↑ = A ↑
        B↑ : A↑ -> Set1
        B↑ a = (B (unemb a)) ↑
        unembΣ : Σ1 A↑ B↑ -> (Σ A B)
        unembΣ x = unemb (split1 _ (λ a b → emb (unemb a , unemb b)) x)
        embΣ : (Σ A B) -> Σ1 A↑ B↑
        embΣ x = (emb (fst x)) , (emb (snd x))
        C↑ : Σ1 A↑ B↑ → Set1
        C↑ x = C (unembΣ x)
        step↑ : (a : A↑) (b : B↑ a) → C↑ (a , b)
        step↑ a b = step (unemb a) (unemb b)                         
---------------------------------------------------------------------
-----

-- Now + can be defined with large elimination ----------------------
_+_ : (A B : Set) -> Set
A + B = Σ Two (λ x → if x then A else B)

inl : {A B : Set} -> A -> A + B
inl a = tt , a

inr : {A B : Set} -> B -> A + B
inr b = ff , b

[_,_] : {A B : Set} -> {C : A + B -> Set1} ->
                        (f : (a : A) -> C (inl a)) ->
                        (g : (b : B) -> C (inr b)) ->
                        (x : A + B) -> C x
[_,_] {C = C} f g 
  = split01 C (λ x → if_then_else_ {λ x → (y : _) -> C (x , y)} x
                                   (λ a → f a)
                                   (λ b → g b))
---------------------------------------------------------------------

