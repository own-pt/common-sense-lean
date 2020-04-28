/- Spatial Reasoning Problem 13 -/
/- It can be found at: SpatialQs.txt -/

/- (13) A is on the right of B
    C is on the left of B.
    D is in front of C.
    E is in front of B.
    Therefore D is on the left of E.-/

/-  a. Left (x,y) & Front (z, x) + Left (front (z, x), y), where the right-hand
    side signifies “z is in front of x, all of which is on the left of y.”

    b. Left (x, y) & Front (z, y) + Left (x,front (z, y)), where the right-hand
    side signifies “x is on the left of z which is in front of y.”

    c. Left (x, y) & Left (u, z) -+ Left (x, left(x, z)).

    d. Left (x, y) * Right (y, x).

    e. Left (front (x, y), z) + Left (x, z) & Left (y, z) & Front (x, y).

    f. Left (x, front (v, z)) -+ Left (x, y) & Left (x, z) & Front (y, z).

    g. Left (x, left (y, z)) + Left (x, y) & Left (x, z) 8~ Left 01, z).

    h. Left (x, y) + - Right (x, y).

    i. Right (x, y) + - Left (x, y). -/


constant U : Type

constants Left Right Front Behind PositionalAttribute TransitivePositionalAttribute
OppositeDirection : U
constant ins : U → U → Prop
constant orientation : U → U → U → Prop
constant holds : U → U → U → Prop

/- axiom from sumo -/
-- (instance Left PositionalAttribute)
axiom left_positional_attribute : ins Left PositionalAttribute

-- (instance Left PositionalAttribute)
axiom right_positional_attribute : ins Right PositionalAttribute

--(=>
--    (and
--        (orientation ?OBJ1 ?OBJ2 ?DIR)
--        (instance ?DIR PositionalAttribute)
--        (oppositeDirection ?DIR ?OPPDIR))
--    (orientation ?OBJ2 ?OBJ1 ?OPPDIR))
axiom oposite_positional : ∀ OBJ1 OBJ2 DIR OPPDIR,
    (orientation OBJ1 OBJ2 DIR)
    ∧ (ins DIR PositionalAttribute)
    ∧ (holds OppositeDirection DIR OPPDIR)
    → (orientation OBJ2 OBJ1 OPPDIR)

/- axioms to be added to SUMO -/
-- (instance Front PositionalAttribute)
-- (instance Front TransitivePositionalAttribute)
axiom front_positional_attribute : ins Front PositionalAttribute
axiom front_transitive_positional_attribute : ins Behind TransitivePositionalAttribute

-- (instance Behind PositionalAttribute)
-- (instance Behind TransitivePositionalAttribute)
axiom behind_positional_attribute : ins Behind PositionalAttribute
axiom behind_transitive_positional_attribute : ins Behind TransitivePositionalAttribute

-- there are some axioms analogous to be added,
-- like "right_front_right" or "right_behid_right"
axiom left_front_left : ∀ OBJ1 OBJ2 OBJ3,
    (orientation OBJ1 OBJ2 Left)
    ∧ (orientation OBJ3 OBJ2 Front)
    → (orientation OBJ1 OBJ3 Left)
axiom right_front_right : ∀ OBJ1 OBJ2 OBJ3,
    (orientation OBJ1 OBJ2 Right)
    ∧ (orientation OBJ3 OBJ2 Front)
    → (orientation OBJ1 OBJ3 Right)

-- next axiom was introduced in problem 06
-- (instance North TransitivePositionalAttribute)
axiom transitive_positional_attribute : ∀ A B C P, (orientation A B P)
    ∧ (orientation B C P)
    ∧ (ins P TransitivePositionalAttribute)
    → (orientation A C P)

-- (OppositeDirection Left Right)
axiom left_opposite_right : holds OppositeDirection Left Right

-- a reasonable property about opposites directions
axiom opposite_directions : ∀ DIR OPDIR,
    (holds OppositeDirection DIR OPDIR)
    → (holds OppositeDirection OPDIR DIR)


/- axioms from problem -/
constants A B C D E : U
axiom a1 : orientation A B Right
axiom a2 : orientation C B Left
axiom a3 : orientation D C Front
axiom a4 : orientation E B Front


/- demonstration start -/
theorem D_is_on_the_left_of_E : orientation D E Left :=
begin
    have h1, from (left_front_left _ _ _) ⟨a2,a4⟩,
    have h2, from (oposite_positional _ _ _ _)
        ⟨h1,⟨left_positional_attribute, left_opposite_right⟩⟩,
    have h3, from (right_front_right _ _ _) ⟨h2,a3⟩,
    have h4, from (opposite_directions _ _) left_opposite_right,

    exact (oposite_positional _ _ _ _) ⟨h3,⟨right_positional_attribute, h4⟩⟩
end
