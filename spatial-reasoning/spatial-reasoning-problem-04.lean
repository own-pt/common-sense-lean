/- Spatial Reasoning Problem 04 -/
/- it can be found at: SpatialQs.txt -/

/- (4) John is carrying a vase.  There is a flower in the vase.  Is John carrying a flower?-/

constant U : Type

constants John Inside Carrying Flower Container Transfer On : U
constant objectTransferred : U → U → Prop
constant orientation : U → U → U → Prop
constant subclass : U → U → Prop
constant agent : U → U → Prop
constant ins : U → U → Prop



/- axioms from SUMO -/
axiom a1 : ∀ VAR1 VAR2 VAR3, (orientation VAR2 VAR1 Inside)
    ∧ (objectTransferred VAR3 VAR1) ∧ (ins VAR3 Transfer)
    → (objectTransferred VAR3 VAR2)
axiom a2 : subclass Carrying Transfer
axiom a3 : ∀ X Y Z, (subclass X Y) ∧ (ins Z X) → (ins Z Y)

/- axioms from problem -/
axiom a4 : ∃ C V F, (ins C Carrying) ∧ (objectTransferred C V)
    ∧ (agent C John) ∧ (ins F Flower) ∧ (ins V Container)
    ∧ (orientation F V Inside)

/- axioms to be added to SUMO -/
axiom a5 : ∀ T O O2, (ins T Transfer) ∧ (objectTransferred T O)
    ∧ (orientation O2 O Inside) → (objectTransferred T O2)
axiom a6 : ∀ T O O2, (ins T Transfer) ∧ (objectTransferred T O)
    ∧ (orientation O O2 On) → (objectTransferred T O2)

/- demonstration start -/
theorem john_is_carrying_a_flower : ∃ C F, (ins C Carrying)
∧ (agent C John) ∧ (ins F Flower) ∧ (objectTransferred C F) :=
begin
    apply exists.elim a4, assume C r1,
    apply exists.elim r1, assume V r2,
    apply exists.elim r2, assume F h,
    have h1, from h.left,
    have h2, from h.right.right.left,
    have h3, from h.right.right.right.left,

    have s1, from (a3 _ _ _) ⟨a2,h1⟩,
    have s2, from h.right.left,
    have s3, from h.right.right.right.right.right,
    have h4, from (a5 _ _ _) ⟨s1,⟨s2,s3⟩⟩,

    have h5 : ∃ F, ins C Carrying ∧ agent C John
        ∧ ins F Flower ∧ objectTransferred C F,
        from exists.intro F ⟨h1,⟨h2,⟨h3,h4⟩⟩⟩,
    have h6 : ∃ C F, ins C Carrying ∧ agent C John
        ∧ ins F Flower ∧ objectTransferred C F,
        from exists.intro C h5,

    assumption
end
