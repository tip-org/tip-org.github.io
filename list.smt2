(declare-datatype
  list
  (par (a)
    ((nil) (cons (head a) (tail (list a))))))
(define-fun-rec
  append (par (a) (((xs (list a)) (ys (list a))) (list a)))
  (match xs
    ((nil (_ nil a))
     ((cons x xs) (cons x (append xs ys))))))
(prove
  (par (a)
    (forall ((xs (list a))) (= (append xs (_ nil a)) xs))))
