/- here we add some recurrent, usefull axioms -/

constant U : Type

/- some declarations from SUMO definitions -/
constants DirectionalAttribute PositionalAttribute
North South East West Left Right Above Below Inside Outside: U

constant ins : U → U → Prop
constant subclass : U → U → Prop
constant orientation : U → U → U → Prop
constant OppositeDirection : U → U → Prop


/- axioms from SUMO -/


/- new definitions and axioms from spatial -/
constant TransitivePositionalAttribute Front Behind : U

-- (OppositeDirection North South)

-- (instance North DirectionalAttribute)
axiom north_is_direcional_attribute :
    ins North DirectionalAttribute


-- (<=>
--    (orientation ?OBJ1 ?OBJ2 North)
--    (orientation ?OBJ2 ?OBJ1 South))
axiom north_south : ∀ OBJ1 OBJ2,
    (orientation OBJ1 OBJ2 North) ↔
    (orientation OBJ2 OBJ1 South)


-- (=>
--    (and
--        (orientation ?OBJ1 ?OBJ2 ?DIR)
--        (instance ?DIR PositionalAttribute)
--        (OppositeDirection ?DIR ?OPPDIR))
--    (orientation ?OBJ2 ?OBJ1 ?OPPDIR))
axiom oposite_directions : ∀ OBJ1 OBJ2 DIR OPPDIR,
    (orientation OBJ1 OBJ2 DIR)
    ∧ (ins DIR PositionalAttribute)
    ∧ (OppositeDirection DIR OPPDIR)
    → (orientation OBJ2 OBJ1 OPPDIR)

-- (OppositeDirection East West)
-- (OppositeDirection Northeast Southwest)
-- (OppositeDirection Upstream Downstream)
-- (OppositeDirection Front Behind)
-- (OppositeDirection Left Right)


-- (subclass TransitivePositionalAttribute PositionalAttribute)
axiom transitive_positional_attribute_is_positional_attribute :
    subclass TransitivePositionalAttribute PositionalAttribute

-- (instance North TransitivePositionalAttribute)
-- (instance South TransitivePositionalAttribute)
-- (instance East TransitivePositionalAttribute)
-- (instance West TransitivePositionalAttribute)
axiom north_transitivepositionalattribute :
    ins North TransitivePositionalAttribute
axiom south_transitivepositionalattribute :
    ins South TransitivePositionalAttribute
axiom east_transitivepositionalattribute :
    ins East TransitivePositionalAttribute
axiom west_transitivepositionalattribute :
    ins West TransitivePositionalAttribute
axiom west_transitivepositionalattribute :
    ins Front TransitivePositionalAttribute
axiom west_transitivepositionalattribute :
    ins Behind TransitivePositionalAttribute

-- (=>
--  (and
--    (orientation ?A ?B ?P)
--    (orientation ?B ?C ?P)
--    (instance ?P TransitivePositionalAttribute))
--  (orientation ?A ?C ?P))
axiom transitive_positional_attribute : ∀ A B C P,
    (orientation A B P)
    ∧ (orientation B C P)
    ∧ (ins P TransitivePositionalAttribute)
