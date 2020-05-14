/-

;; A. Bear and Big Brother Problem
;; https://codeforces.com/problemset/problem/791/A

(loop for x = 4 then (* x 3)
      for y = 9 then (* y 2)
      until (> x y)
      collect (cons x y))

Theorem?

A) exists p in CL | p: range(1,10) x range(1,10) -> nat and for any a, b
in range(1,10) x range(1,10) it holds that 

p(a, b) = inf set(n in nat | 2^n a > 3^n b)

B) there exists such p that has size < 1kb, runs in stack < 1kb and
terminates in less than 1k evaluation steps

C) Mario Carneiro: well, you could define that as a lean function and
prove that it has a given value. 

https://leanprover.zulipchat.com/#narrow/stream/187764-Lean-for.20teaching/topic/from.20algorithms.20to.20proofs
-/

def compute : ℕ → ℕ → ℕ := 
