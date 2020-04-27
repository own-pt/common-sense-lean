/- Spatial Reasoning Problem 01 -/
/- It can be found at: github.com/ontologyportal/sumo/blob/master/tests/SpatialQs.txt -/

-- (6) A bookcase is on the floor.  A book is on the bookcase.  Is the book higher than the floor?

universe V
constant U : Type

constants Right Left Book Furniture Floor On  TransitivePositionalAttribute PositionalAttribute Above : U
constant ins : U → U → Prop
constant located : U → U → Prop
constant subclass : U → U → Prop
constant orientation: U → U → U → Prop

/-
(exists (?B ?F ?BOOK)
  (and
    (instance ?BOOK Book)
    (instance ?B Furniture)
    (instance ?F Floor)
    (orientation ?B ?F On)
    (orientation ?BOOK ?B On)))
-/
axiom a1 : ∃ b f book : U , 
  ins book Book ∧
  ins b Furniture ∧
  ins f Floor ∧ 
  orientation b f On ∧
  orientation book b On

/-
(subclass TransitivePositionalAttribute PositionalAttribute)
-/
axiom a2 : subclass TransitivePositionalAttribute PositionalAttribute

/-
(=>
  (and
    (orientation ?A ?B ?P)
    (orientation ?B ?C ?P)
    (instance ?P TransitivePositionalAttribute))
  (orientation ?A ?C ?P))
-/
axiom a3 : ∀ a b c p : U,
  (orientation a b p ∧
  orientation b c p ∧
  ins p TransitivePositionalAttribute) → 
    orientation a c p

/-
(=>
  (and
    (orientation ?A ?B On)
    (orientation ?B ?C On))
  (orientation ?A ?C Above))
-/
axiom a4 : ∀ a b c : U,
  orientation a b On ∧ orientation b c On →
    orientation a c Above

theorem book_above_floor : ∃ (book : U) (f : U), orientation book f Above :=
begin
  apply exists.elim a1, assume b  h1,
  apply exists.elim h1, assume f  h2,    
  apply exists.elim h2, assume book  h3,  
  apply exists.intro book, apply exists.intro f,
    apply a4 book b f,
      split,
        exact h3.right.right.right.right,
        exact h3.right.right.right.left
end
