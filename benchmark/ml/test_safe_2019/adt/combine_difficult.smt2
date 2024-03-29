(set-logic HORN)
(set-info :source |
  Benchmark: /home/katsura/hflmc2/benchmark/ml/test_safe_2019/adt/combine_difficult.ml
  Generated by MoCHi
|)
(set-info :status unknown)
(declare-fun |fail_195[0:0]| ( Int) Bool)
(declare-fun |combine[0:2]| ( Int  Int) Bool)
(declare-fun |length[0:2][0:0]| ( Int  Int) Bool)
(declare-fun |length[0:0]| ( Int) Bool)
(declare-fun |make_int_list[0:2][0:0]| ( Int  Int  Int) Bool)
(declare-fun |make_int_list[0:1]| ( Int  Int) Bool)
(declare-fun |make_int_list_23[0:1][0:0]| ( Int  Int) Bool)
(declare-fun |make_int_list_23[0:0]| ( Int) Bool)
(assert (not (exists ((x0 Int)) (|fail_195[0:0]| x0))))
(assert (forall ((x0 Int)(x1 Int)(x2 Int)) (=> (and (|combine[0:2]| x1 x2) (or (and (>= x1 1) (<= x2 0)) (and (>= x2 1) (<= x1 0)))) (|fail_195[0:0]| x0))))
(assert (forall ((x0 Int)(x1 Int)(x2 Int)(var2349 Int)(var2350 Int)) (=> (and (|length[0:2][0:0]| x1 x2) (and (|length[0:2][0:0]| x0 x2) (and (|make_int_list_23[0:1][0:0]| var2349 x0) (|make_int_list[0:2][0:0]| x0 var2350 x1)))) (|combine[0:2]| x0 x1))))
(assert (forall ((x1 Int)(x2 Int)(var2351 Int)(var2352 Int)) (=> (and (|length[0:2][0:0]| var2351 var2352) (and (|length[0:0]| x1) (and (>= x1 1) (and (= (+ 1 var2351) x1) (= x2 (+ 1 var2352)))))) (|length[0:2][0:0]| x1 x2))))
(assert (forall ((x1 Int)(x0 Int)) (=> (and (|length[0:0]| x1) (and (= x0 0) (<= x1 0))) (|length[0:2][0:0]| x1 x0))))
(assert (forall ((x1 Int)(x0 Int)) (=> (and (|length[0:0]| x0) (and (= (+ 1 x1) x0) (>= x0 1))) (|length[0:0]| x1))))
(assert (forall ((x1 Int)(x0 Int)(x2 Int)(var2353 Int)(var2354 Int)) (=> (and (|length[0:2][0:0]| x0 x2) (and (|make_int_list_23[0:1][0:0]| var2353 x0) (|make_int_list[0:2][0:0]| x0 var2354 x1))) (|length[0:0]| x1))))
(assert (forall ((x1 Int)(x2 Int)(var2355 Int)(var2356 Int)) (=> (and (|length[0:2][0:0]| var2355 var2356) (and (|length[0:0]| x1) (and (>= x1 1) (and (= (+ 1 var2355) x1) (= x2 (+ 1 var2356)))))) (|length[0:2][0:0]| x1 x2))))
(assert (forall ((x1 Int)(x0 Int)) (=> (and (|length[0:0]| x1) (and (= x0 0) (<= x1 0))) (|length[0:2][0:0]| x1 x0))))
(assert (forall ((x1 Int)(x0 Int)) (=> (and (|length[0:0]| x0) (and (= (+ 1 x1) x0) (>= x0 1))) (|length[0:0]| x1))))
(assert (forall ((x0 Int)(var2357 Int)(var2358 Int)(x1 Int)) (=> (and (|make_int_list_23[0:1][0:0]| var2357 x0) (|make_int_list[0:2][0:0]| x0 var2358 x1)) (|length[0:0]| x0))))
(assert (forall ((x0 Int)(x1 Int)(x2 Int)(var2360 Int)(var2359 Int)) (=> (and (|make_int_list[0:2][0:0]| x0 var2359 var2360) (and (|make_int_list[0:1]| x0 x1) (= x2 (+ 1 var2360)))) (|make_int_list[0:2][0:0]| x0 x1 x2))))
(assert (forall ((x0 Int)(x1 Int)(x2 Int)) (=> (and (|make_int_list[0:1]| x0 x1) (= x2 0)) (|make_int_list[0:2][0:0]| x0 x1 x2))))
(assert (forall ((x1 Int)(x0 Int)(x2 Int)) (=> (|make_int_list[0:1]| x1 x2) (|make_int_list[0:1]| x1 x0))))
(assert (forall ((x1 Int)(x0 Int)(var2361 Int)) (=> (|make_int_list_23[0:1][0:0]| var2361 x1) (|make_int_list[0:1]| x1 x0))))
(assert (forall ((x0 Int)(x1 Int)(var2363 Int)(var2362 Int)) (=> (and (|make_int_list_23[0:1][0:0]| var2362 var2363) (and (|make_int_list_23[0:0]| x0) (= x1 (+ 1 var2363)))) (|make_int_list_23[0:1][0:0]| x0 x1))))
(assert (forall ((x0 Int)(x1 Int)) (=> (and (|make_int_list_23[0:0]| x0) (= x1 0)) (|make_int_list_23[0:1][0:0]| x0 x1))))
(assert (forall ((x0 Int)(x2 Int)) (=> (|make_int_list_23[0:0]| x2) (|make_int_list_23[0:0]| x0))))
(assert (forall ((x0 Int)) (|make_int_list_23[0:0]| x0)))
(check-sat)
(get-model)
(exit)
