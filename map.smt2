(declare-datatype
  list
  (par (a)
    ((nil) (cons (head a) (tail (list a))))))
(define-fun-rec
  map (par (a b) (((f (=> a b)) (xs (list a))) (list b)))
  (match xs
     ((nil (_ nil b))
      ((cons y ys) (cons (@ f y) (map f ys))))))
(prove
  (par (a b c)
    (forall ((f (=> b c)) (g (=> a b)) (xs (list a)))
      (= (map (lambda ((x a)) (@ f (@ g x))) xs)
        (map f (map g xs))))))
