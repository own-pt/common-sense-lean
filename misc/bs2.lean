/-
The problem is originally presented in:
A. Pease, G. Sutcliffe, N. Siegel, and S. Trac, “Large Theory
Reasoning with SUMO at CASC,” pp. 1–8, Jul. 2009.
Here we present the natural deduction proof in Lean.
-/

import bs_test

-- some initial tests

lemma VertebrateAnimal : ∀ (x : U), ins x Vertebrate → ins x Animal := 
begin 
 intros a h,
 have h1, from a15 Vertebrate Animal a,
 apply h1,
 exact (and.intro a71402 a72771),
 exact (and.intro a71382 h)
end

lemma subclass_TransitiveRelation : ins subclass_m TransitiveRelation :=
begin
 --specialize a15 PartialOrderingRelation TransitiveRelation subclass_m,
 apply a15,
 exact ⟨ a72180, a71844 ⟩, 
 exact ⟨ a67818, a13 ⟩, 
end

lemma VertebrateOrganism : ∀ (x : U), ins x Vertebrate → ins x Organism := 
begin 
 intros a h,
 have h1, from a15 Animal Organism a, 
 apply h1,
 exact and.intro a72771 a71371,
 have h0 : ∀ x, ins x Vertebrate → ins x Animal, apply VertebrateAnimal; assumption,
 have h2, from h0 a h,
 exact and.intro a71369 h2,
end

lemma VertebrateOrganism' : ∀ (x : U), ins x Vertebrate → ins x Organism := 
begin
  intros a h,
  have h₁ : ins subclass_m TransitiveRelation,
    --specialize a15 PartialOrderingRelation TransitiveRelation subclass_m,
    apply a15,
    exact ⟨a72180, a71844⟩, 
    exact ⟨a67818, a13⟩, 
  have h₂ : subclass Vertebrate Organism,
    apply a67809 _ Animal _,
    exact ⟨a71402, ⟨a72771, a71371⟩⟩,
    exact h₁,
    exact ⟨a71382, a71369⟩,
  apply a15 Vertebrate _ _,
  exact ⟨a71402, a71371⟩,
  exact ⟨h₂, h⟩
end

lemma VertebrateEntity : ∀ (x : U), ins x Vertebrate → ins x Entity := 
begin
  intros a h, 
  have h1, apply subclass_TransitiveRelation; assumption,
  have h2 : subclass Vertebrate Organism,
    apply a67809 _ Animal _,
    exact ⟨a71402, ⟨ a72771, a71371 ⟩⟩,
    exact h1,
    exact ⟨a71382, a71369⟩,  
  have h3 : subclass Vertebrate Agent,
    apply a67809 _ Organism _,
    exact ⟨a71402, ⟨ a71371, a71872 ⟩⟩,
    exact h1,
    exact ⟨h2, a71340⟩,
  have h4 : subclass Vertebrate Object,
    apply a67809 _ Agent _,
    exact ⟨a71402, ⟨ a71872, a71669 ⟩⟩,
    exact h1,
    exact ⟨h3, a67315⟩,
  have h5 : subclass Vertebrate Physical,
    apply a67809 _ Object _,
    exact ⟨a71402, ⟨ a71669, a69763 ⟩⟩,
    exact h1,
    exact ⟨h4, a67177⟩,
  have h6 : subclass Vertebrate Entity,
    apply a67809 _ Physical _,
    exact ⟨a71402, ⟨ a69763, a67331 ⟩⟩,
    exact h1,
    exact ⟨ h5, a67174 ⟩,
  apply a15 Vertebrate _ _,
  exact ⟨a71402, a67331⟩,
  exact ⟨h6, h⟩
end

-- start proofs

lemma listLemma (hne : nonempty U) : ∀ x y z : U, 
  ins x Entity ∧ ins y Entity ∧ ins z Entity →
  inList x (ListFn2 y z) → x = y ∨ x = z :=
begin
  intros x y z h h1,
    rw (a72767 y z ⟨h.right.left, h.right.right⟩) at h1,
    have h2 : x = y ∨ inList x (ConsFn z NullList_m),
      rw ←(a72770 (ConsFn z NullList_m) x y),
      exact h1,
      simp *,
      apply novo1 z NullList_m,
        apply a15 Abstract Entity NullList_m,
          --simp *,
            --apply a15 Relation Abstract NullList_m;
            --  simp *,
            --  apply a15 List Relation NullList_m;
            --    simp *,
            --    assumption,
          exact ⟨a68771, a67331⟩,
          have h3, from a15 _ _ _ ⟨a67958, a68763⟩ ⟨a67954, a67959⟩,
          exact ⟨a67332, a15 _ _ _ ⟨a68763, a68771⟩ ⟨a67450, h3⟩⟩, 
          exact a67959,
      cases h2,
        exact or.inl h2,
        have h3 : x = z ∨ inList x NullList_m,
          rw ←(a72770 NullList_m x z),
          exact h2,
          exact ⟨h.1, ⟨h.2.2, a67959⟩⟩,
          cases h3,
            exact or.inr h3,
            apply false.elim,
              exact ((a72769 x) h.left) h3
end


lemma lX (hne : nonempty U) : ∀ x c c1 c2,
  (ins c SetOrClass ∧ ins c1 SetOrClass ∧ ins c2 SetOrClass) →
  (ins c Class ∧ ins c1 Class ∧ ins c2 Class ∧ ins x Entity) → 
    (partition3 c c1 c2 ∧ ins x c ∧ ¬ ins x c1) → ins x c2 := 
begin
  intros a c c1 c2 h1 h2 h3,
  have a67131', from a67131 c c1 c2,
  have a67115', from a67115 c1 c2 c a,
  have h₃, from a67131' ⟨ h2.1, ⟨h2.2.1, h2.2.2.1 ⟩⟩,
  have h4, from iff.elim_left h₃ h3.1,
  cases h4 with h4a h4b,
  cases a67115' with b h5,
  have h7, from h5.right,
  have h8, from h2.right.right.right,
  specialize h7 h8,
  have h9 : subclass SetOrClass Entity,
    apply (a67809 _ Abstract _), 
      exact ⟨a67448, ⟨a68771, a67331⟩⟩,
      apply subclass_TransitiveRelation; assumption,
      exact ⟨a67446, a67332⟩,
  have h10 : ins c1 Entity,
    apply (a15 SetOrClass _ _), 
      exact ⟨a67448, a67331⟩,
      exact ⟨h9, h1.2.1⟩,
  have h11 : ins c2 Entity,
    apply (a15 SetOrClass _ _), 
      exact ⟨a67448, a67331⟩,
      exact ⟨h9, h1.2.2⟩,
  specialize h7 ⟨h1.1, ⟨h2.1, ⟨h2.2.1, ⟨h10, ⟨h2.2.2.1, h11⟩⟩⟩⟩⟩,
  specialize h7 h4a,
  specialize h7 h3.right.left,
  have h12 : b = c1 ∨ b = c2,
    apply listLemma, 
      repeat { assumption },
      split,
        apply a15 SetOrClass _ _,
          exact ⟨a67448, a67331⟩,
          exact ⟨h9, h5.left⟩,
      exact ⟨h10, h11⟩,
      exact h7.left,
  cases h12,
    rw h12 at h7,
    apply false.elim,
      exact h3.right.right h7.right,
    rw ←h12,
    exact h7.right
 end


lemma subclass_animal_entity : subclass Animal Entity :=
begin
  have h1, apply subclass_TransitiveRelation; assumption,
  have h2 : subclass Animal Agent,
    apply a67809 _ Organism _,
    exact ⟨a72771, ⟨ a71371, a71872 ⟩⟩,
    exact h1,
    exact ⟨a71369, a71340⟩,
  have h3 : subclass Animal Object,
    apply a67809 _ Agent _,
    exact ⟨a72771, ⟨ a71872, a71669 ⟩⟩,
    exact h1,
    exact ⟨h2, a67315⟩,
  have h4 : subclass Animal Physical,
    apply a67809 _ Object _,
    exact ⟨a72771, ⟨ a71669, a69763 ⟩⟩,
    exact h1,
    exact ⟨h3, a67177⟩,
  apply a67809 _ Physical _,
  exact ⟨a72771, ⟨ a69763, a67331 ⟩⟩,
  exact h1,
  exact ⟨ h4, a67174 ⟩,
end

lemma subclass_vertebrate_entity : subclass Vertebrate Entity :=
begin
  have h1, apply subclass_TransitiveRelation; assumption,
  have h2 : subclass Vertebrate Organism,
    apply a67809 _ Animal _,
    exact ⟨a71402, ⟨ a72771, a71371 ⟩⟩,
    exact h1,
    exact ⟨a71382, a71369⟩,  
  have h3 : subclass Vertebrate Agent,
    apply a67809 _ Organism _,
    exact ⟨a71402, ⟨ a71371, a71872 ⟩⟩,
    exact h1,
    exact ⟨h2, a71340⟩,
  have h4 : subclass Vertebrate Object,
    apply a67809 _ Agent _,
    exact ⟨a71402, ⟨ a71872, a71669 ⟩⟩,
    exact h1,
    exact ⟨h3, a67315⟩,
  have h5 : subclass Vertebrate Physical,
    apply a67809 _ Object _,
    exact ⟨a71402, ⟨ a71669, a69763 ⟩⟩,
    exact h1,
    exact ⟨h4, a67177⟩,
  apply a67809 _ Physical _,
  exact ⟨a71402, ⟨ a69763, a67331 ⟩⟩,
  exact h1,
  exact ⟨ h5, a67174 ⟩,
end

lemma subclass_invertebrate_entity : subclass Invertebrate Entity :=
begin
  have h1, apply subclass_TransitiveRelation; assumption,
  have h2 : subclass Invertebrate Organism,
    apply a67809 _ Animal _,
    exact ⟨a72778, ⟨ a72771, a71371 ⟩⟩,
    exact h1,
    exact ⟨a71383, a71369⟩,  
  have h3 : subclass Invertebrate Agent,
    apply a67809 _ Organism _,
    exact ⟨a72778, ⟨ a71371, a71872 ⟩⟩,
    exact h1,
    exact ⟨h2, a71340⟩,
  have h4 : subclass Invertebrate Object,
    apply a67809 _ Agent _,
    exact ⟨a72778, ⟨ a71872, a71669 ⟩⟩,
    exact h1,
    exact ⟨h3, a67315⟩,
  have h5 : subclass Invertebrate Physical,
    apply a67809 _ Object _,
    exact ⟨a72778, ⟨ a71669, a69763 ⟩⟩,
    exact h1,
    exact ⟨h4, a67177⟩,
  apply a67809 _ Physical _,
  exact ⟨a72778, ⟨ a69763, a67331 ⟩⟩,
  exact h1,
  exact ⟨ h5, a67174 ⟩,
end

lemma ins_banana_entity : ins BananaSlug10 Entity := 
begin
 have h1, apply subclass_TransitiveRelation; assumption,
 have h2 : ins BananaSlug10 Organism, 
  --specialize a15 Animal Organism BananaSlug10,
  apply a15,
  exact and.intro a72771 a71371,
  exact and.intro a71369 a72772,
 have h3 : ins BananaSlug10 Agent, 
  --specialize a15 Organism Agent BananaSlug10,
  apply a15,
  exact and.intro a71371 a71872,
  exact and.intro a71340 h2,
 have h4 : ins BananaSlug10 Object, 
  --specialize a15 Agent Object BananaSlug10,
  apply a15,
  exact and.intro a71872 a71669,
  exact and.intro a67315 h3,
 have h5 : ins BananaSlug10 Physical, 
  --specialize a15 Object Physical BananaSlug10,
  apply a15,
  exact and.intro a71669 a69763,
  exact and.intro a67177 h4,
 --specialize a15 Physical Entity BananaSlug10,
 apply a15,
 exact and.intro a69763 a67331,
 exact and.intro a67174 h5,
end

lemma ins_animal_class : ins Animal Class :=
begin
 have h0 : subclass Animal Entity,
  apply subclass_animal_entity; assumption,
 have h1, from (a67173 Animal),
 exact h1.2 h0,
end


--lemma l0' (hne : nonempty U) : ¬(ins BananaSlug10 Vertebrate) := by simp *
lemma l0  (hne : nonempty U) : ¬(ins BananaSlug10 Vertebrate) :=
begin
  have a72773', from a72773 BananaSlug10,
  exact a72773' (and.intro a72772 a72774)
end

theorem Banana_Invertebrate (hne: nonempty U) : ins BananaSlug10 Invertebrate :=
begin
 have h1 : ¬ ins BananaSlug10 Vertebrate,
  apply l0; assumption,
 have h2 : ∀ x c c1 c2,
  (ins c SetOrClass ∧ ins c1 SetOrClass ∧ ins c2 SetOrClass) →
  (ins c Class ∧ ins c1 Class ∧ ins c2 Class ∧ ins x Entity) → 
   (partition3 c c1 c2 ∧ ins x c ∧ ¬ ins x c1) → ins x c2, 
   apply lX; assumption,
 have h3, from h2 BananaSlug10 Animal Vertebrate Invertebrate,
 apply h3,
 exact ⟨ a72771, ⟨ a71402, a72778 ⟩⟩,
 have h₁ : subclass Animal Entity, 
   apply subclass_animal_entity; assumption,
 have h₂ : ins Animal Class,
   rw a67173, exact h₁,
 have h₃ : subclass Vertebrate Entity,
   apply subclass_vertebrate_entity; assumption,
 have h₄ : ins Vertebrate Class, 
   rw a67173, exact h₃,
 have h₅ : subclass Invertebrate Entity,
   apply subclass_invertebrate_entity; assumption,
 have h₆ : ins Invertebrate Class, 
  rw a67173, exact h₅,
 have h₇ : ins BananaSlug10 Entity, 
  apply ins_banana_entity; assumption,
 exact and.intro h₂ (and.intro h₄ (and.intro h₆ h₇)),
 exact and.intro a71370 (and.intro a72772 h1),
end
