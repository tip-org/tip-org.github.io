(declare-datatype Nat ((Zero) (Succ (pred Nat))))
(define-fun-rec
  plus ((x Nat) (y Nat)) Nat
  (match x
    ((Zero y)
     ((Succ n) (Succ (plus n y))))))
(prove (forall ((n Nat) (m Nat)) (= (plus n m) (plus m n))))
