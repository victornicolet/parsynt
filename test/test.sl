(set-logic LIA)
(define-fun max ((x Int)
  (y Int))
  Int
  (ite (> x y) x y))

(define-fun f_cl_0 ((cl Int)
  (a0 Bool))
  Int
  (ite a0 (+ cl 1) 0))

(define-fun f_cl_1 ((cl Int)
  (a0 Bool)
  (a1 Bool))
  Int
  (ite a1 (+ (f_cl_0 cl a0) 1) 0))

(define-fun f_cl_2 ((cl Int)
  (a0 Bool)
  (a1 Bool)
  (a2 Bool))
  Int
  (ite a2 (+ (f_cl_1 cl a0 a1) 1) 0))

(define-fun f_cl_3 ((cl Int)
  (a0 Bool)
  (a1 Bool)
  (a2 Bool)
  (a3 Bool))
  Int
  (ite a3 (+ (f_cl_2 cl a0 a1 a2) 1) 0))

(define-fun f_cl_4 ((cl Int)
  (a0 Bool)
  (a1 Bool)
  (a2 Bool)
  (a3 Bool)
  (a4 Bool))
  Int
  (ite a4 (+ (f_cl_3 cl a0 a1 a2 a3) 1) 0))

(define-fun f_cl_5 ((cl Int)
  (a0 Bool)
  (a1 Bool)
  (a2 Bool)
  (a3 Bool)
  (a4 Bool)
  (a5 Bool))
  Int
  (ite a5 (+ (f_cl_4 cl a0 a1 a2 a3 a4) 1) 0))

(define-fun f_ml_0 ((ml Int)
  (cl Int)
  (a0 Bool))
  Int
  (max ml (ite a0 (+ cl 1) 0)))

(define-fun f_ml_1 ((ml Int)
  (cl Int)
  (a0 Bool)
  (a1 Bool))
  Int
  (max (f_ml_0 ml (f_cl_0 cl a0) a0) (ite a1 (+ (f_cl_0 cl a0) 1) 0)))

(define-fun f_ml_2 ((ml Int)
  (cl Int)
  (a0 Bool)
  (a1 Bool)
  (a2 Bool))
  Int
  (max (f_ml_1 ml (f_cl_1 cl a0 a1) a0 a1)
  (ite a2 (+ (f_cl_1 cl a0 a1) 1) 0)))

(define-fun f_ml_3 ((ml Int)
  (cl Int)
  (a0 Bool)
  (a1 Bool)
  (a2 Bool)
  (a3 Bool))
  Int
  (max (f_ml_2 ml (f_cl_2 cl a0 a1 a2) a0 a1 a2)
  (ite a3 (+ (f_cl_2 cl a0 a1 a2) 1) 0)))

(define-fun f_ml_4 ((ml Int)
  (cl Int)
  (a0 Bool)
  (a1 Bool)
  (a2 Bool)
  (a3 Bool)
  (a4 Bool))
  Int
  (max (f_ml_3 ml (f_cl_3 cl a0 a1 a2 a3) a0 a1 a2 a3)
  (ite a4 (+ (f_cl_3 cl a0 a1 a2 a3) 1) 0)))

(define-fun f_ml_5 ((ml Int)
  (cl Int)
  (a0 Bool)
  (a1 Bool)
  (a2 Bool)
  (a3 Bool)
  (a4 Bool)
  (a5 Bool))
  Int
  (max (f_ml_4 ml (f_cl_4 cl a0 a1 a2 a3 a4) a0 a1 a2 a3 a4)
  (ite a5 (+ (f_cl_4 cl a0 a1 a2 a3 a4) 1) 0)))

(define-fun f_cj_0 ((cj Bool)
  (a0 Bool))
  Bool
  (and a0 cj))

(define-fun f_cj_1 ((cj Bool)
  (a0 Bool)
  (a1 Bool))
  Bool
  (and a1 (f_cj_0 cj a0)))

(define-fun f_cj_2 ((cj Bool)
  (a0 Bool)
  (a1 Bool)
  (a2 Bool))
  Bool
  (and a2 (f_cj_1 cj a0 a1)))

(define-fun f_cj_3 ((cj Bool)
  (a0 Bool)
  (a1 Bool)
  (a2 Bool)
  (a3 Bool))
  Bool
  (and a3 (f_cj_2 cj a0 a1 a2)))

(define-fun f_cj_4 ((cj Bool)
  (a0 Bool)
  (a1 Bool)
  (a2 Bool)
  (a3 Bool)
  (a4 Bool))
  Bool
  (and a4 (f_cj_3 cj a0 a1 a2 a3)))

(define-fun f_cj_5 ((cj Bool)
  (a0 Bool)
  (a1 Bool)
  (a2 Bool)
  (a3 Bool)
  (a4 Bool)
  (a5 Bool))
  Bool
  (and a5 (f_cj_4 cj a0 a1 a2 a3 a4)))

(define-fun f_c_0 ((c Int)
  (cj Bool)
  (a0 Bool))
  Int
  (ite (and a0 cj) (+ c 1) 0))

(define-fun f_c_1 ((c Int)
  (cj Bool)
  (a0 Bool)
  (a1 Bool))
  Int
  (ite (and a1 (f_cj_0 cj a0)) (+ (f_c_0 c (f_cj_0 cj a0) a0) 1) 0))

(define-fun f_c_2 ((c Int)
  (cj Bool)
  (a0 Bool)
  (a1 Bool)
  (a2 Bool))
  Int
  (ite (and a2 (f_cj_1 cj a0 a1)) (+ (f_c_1 c (f_cj_1 cj a0 a1) a0 a1) 1) 0))

(define-fun f_c_3 ((c Int)
  (cj Bool)
  (a0 Bool)
  (a1 Bool)
  (a2 Bool)
  (a3 Bool))
  Int
  (ite (and a3 (f_cj_2 cj a0 a1 a2))
  (+ (f_c_2 c (f_cj_2 cj a0 a1 a2) a0 a1 a2) 1) 0))

(define-fun f_c_4 ((c Int)
  (cj Bool)
  (a0 Bool)
  (a1 Bool)
  (a2 Bool)
  (a3 Bool)
  (a4 Bool))
  Int
  (ite (and a4 (f_cj_3 cj a0 a1 a2 a3))
  (+ (f_c_3 c (f_cj_3 cj a0 a1 a2 a3) a0 a1 a2 a3) 1) 0))

(define-fun f_c_5 ((c Int)
  (cj Bool)
  (a0 Bool)
  (a1 Bool)
  (a2 Bool)
  (a3 Bool)
  (a4 Bool)
  (a5 Bool))
  Int
  (ite (and a5 (f_cj_4 cj a0 a1 a2 a3 a4))
  (+ (f_c_4 c (f_cj_4 cj a0 a1 a2 a3 a4) a0 a1 a2 a3 a4) 1) 0))
