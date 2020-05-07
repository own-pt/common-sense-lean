/-

From adam's serie:

https://www.youtube.com/watch?v=SkruxPmN0kk
https://www.youtube.com/watch?v=nvHatVfiLPU

-/

constants Entity Hominid Human : Type

constant isHominid : Entity  → Prop
constant hasHair : Entity → Prop

def isHuman (x : Entity) : Prop  := isHominid x ∧ hasHair x

constant hasBirth : { x : Entity // isHominid x } → Prop


