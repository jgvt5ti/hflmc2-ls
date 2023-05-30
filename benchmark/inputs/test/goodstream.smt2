(define-fun-rec length ((ls (List Int))) Int
   (ite (= nil ls) 0 (+ 1 (length (tail ls)))))
(declare-fun X1 (Int (List Int)) Bool)
(declare-fun X2 (Int (List Int)) Bool)
(declare-fun X3 (Int (List Int)) Bool)
(declare-fun X6 (Int Int (List Int)) Bool)
(declare-fun X7 (Int Int (List Int) (List Int)) Bool)
(declare-fun X24 (Int ) Bool)
(declare-fun X27 ( ) Bool)
(declare-fun X28 ( (List Int)) Bool)
(declare-fun X35 (Int (List Int)) Bool)
(declare-fun X36 (Int Int Int (List Int) (List Int)) Bool)
(assert (forall ((x35 Int)(x33 (List Int))) (=> (and (X2  x35  x33) (<=  x35 0)) false)))
(assert (forall ((hd8 Int)(x35 Int)(x33 (List Int))) (=> (X2  x35  x33) (X6  hd8 x35  x33))))
(assert (forall ((u20 Int)(x34 Int)(x33 (List Int))) (=> (and (X2  u20  x33) (X3  x34  x33)) (X1  x34  x33))))
(assert (forall ((hd8 Int)(u7 Int)(ls5 (List Int))(tl9 (List Int))) (=> (X6  hd8 u7  ls5) (X7  hd8 u7  tl9 ls5))))
(assert (forall ((hd8 Int)(tmp36 Int)(u7 Int)(ls5 (List Int))(tl9 (List Int))) (=> (and (=  tmp36 0) (and (X7  hd8 u7  tl9 ls5) (=  ls5 nil))) (X3  tmp36  ls5))))
(assert (forall ((hd8 Int)(tmp37 Int)(u7 Int)(ls5 (List Int))(tl9 (List Int))) (=> (and (=  tmp37 (-  u7 1)) (and (X7  hd8 u7  tl9 ls5) (and (=  hd8 0) (=  ls5 (insert hd8 tl9))))) (X36  tmp37 hd8 u7  tl9 ls5))))
(assert (forall ((hd8 Int)(u7 Int)(x32 Int)(ls5 (List Int))(tl9 (List Int))) (=> (X36  x32 hd8 u7  tl9 ls5) (X2  x32  tl9))))
(assert (forall ((hd8 Int)(u7 Int)(u20 Int)(x31 Int)(ls5 (List Int))(tl9 (List Int))) (=> (and (X36  u20 hd8 u7  tl9 ls5) (X1  x31  tl9)) (X24  x31 ))))
(assert (forall ((ls3 (List Int))) (=> X27 (X28   ls3))))
(assert (forall ((tmp38 Int)(ls3 (List Int))) (=> (and (=  tmp38 (+ 1 (length ls3))) (X28   ls3)) (X35  tmp38  ls3))))
(assert (forall ((x29 Int)(ls3 (List Int))) (=> (X35  x29  ls3) (X2  x29  ls3))))
(assert (forall ((u20 Int)(x28 Int)(ls3 (List Int))) (=> (and (X35  u20  ls3) (X1  x28  ls3)) (X24  x28 ))))
(assert (forall () (=> true X27)))
(check-sat)
(get-model)
    