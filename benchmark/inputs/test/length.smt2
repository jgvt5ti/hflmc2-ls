(define-fun-rec length ((ls (List Int))) Int
   (ite (= nil ls) 0 (+ 1 (length (tail ls)))))
(declare-fun XX (Int (List Int)) Bool)
(assert (forall ((n Int) (ls (List Int))) (=> (XX n ls) (= n (length ls)))))
(assert (forall ((n Int) (ls (List Int))) (=> (= n (length ls)) (XX n ls))))
(check-sat)
(get-model)