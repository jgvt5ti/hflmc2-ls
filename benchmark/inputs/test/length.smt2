(define-fun-rec length ((ls (List Int))) Int
   (ite (= nil ls) 0 (+ 1 (length (tail ls)))))
(declare-fun X1 (Int (List Int)) Bool)
(assert (forall ((n Int) (ls (List Int))) (=> (X1 n ls) (= n (length ls)))))
(assert (forall ((n Int) (ls (List Int))) (=> (= n (length ls)) (X1 n ls))))
(check-sat)
(get-model)