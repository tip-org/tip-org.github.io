(declare-datatypes (a)
  ((list (nil) (cons (head a) (tail (list a))))))
(define-funs-rec
  ((par (a) (append ((xs (list a)) (ys (list a))) (list a))))
  ((match xs
     (case nil (as nil (list a)))
     (case (cons x xs) (cons x (as (append xs ys) (list a)))))))
(assert-not
  (par (a)
    (forall ((xs (list a))) (= (append xs (as nil (list a))) xs))))
(check-sat)
