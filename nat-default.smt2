(declare-datatypes () ((Nat (Zero) (Succ (pred Nat)))))
(define-funs-rec
  ((plus ((x Nat) (y Nat)) Nat))
  ((match x
     (case Zero y)
     (case default (Succ (plus (pred x) y))))))
(assert-not (forall ((n Nat) (m Nat)) (= (plus n m) (plus m n))))
(check-sat)
