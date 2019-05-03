(declare-datatype Nat ((Zero) (Succ (pred Nat))))
(define-fun-rec
  plus ((x Nat) (y Nat)) Nat
  (match x
    ((Zero y)
     (_ (Succ (plus (pred x) y))))))
(prove (forall ((n Nat) (m Nat)) (= (plus n m) (plus m n))))
