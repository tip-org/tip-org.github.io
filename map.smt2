(declare-datatypes (a)
  ((list (nil) (cons (head a) (tail (list a))))))
(define-funs-rec
  ((par (a b) (map2 ((f (=> a b)) (xs (list a))) (list b))))
  ((match xs
     (case nil (as nil (list b)))
     (case (cons y ys) (cons (@ f y) (as (map2 f ys) (list b)))))))
(assert-not
  (par (a b c)
    (forall ((f (=> b c)) (g (=> a b)) (xs (list a)))
      (= (map2 (lambda ((x a)) (@ f (@ g x))) xs)
        (map2 f (map2 g xs))))))
(check-sat)
