(set-logic UF)

(declare-sort U 0) ; Declare U as an uninterpreted sort

; Declare the functions and constants
(declare-fun f (U U) U)
(declare-fun g (U) U)
(declare-const e U)
(declare-const c U)

; Define a function for axiom 1
(define-fun axiom1 ((x U) (y U) (z U)) Bool
  (= (f (f x y) z) (f x (f y z))))

; Define a function for axiom 2
(define-fun axiom2 ((x U)) Bool
  (and (= (f x e) x) (= (f e x) x)))

; Define a function for axiom 3
(define-fun axiom3 ((x U)) Bool
  (and (= (f x (g x)) e) (= (f (g x) x) e)))

; Define a function for \neg \varphi
(define-fun neg_varphi ((x U)) Bool
  (and (= (f x c) x) (= (f c x) x) (not (= e c))))

;
; Instantiated Axiom 1 on ground terms.
;
(assert (forall ((x U) (y U) (z U))
  (=> (and (or (= x e) (= x c))
           (or (= y e) (= y c))
           (or (= z e) (= z c)))
       (axiom1 x y z))))

;
; Instantiated Axiom 2 on ground terms.
;
(assert (forall ((x U))
  (=> (or (= x e) (= x c))
      (axiom2 x))))

;
; Instantiated Axiom 3 on ground terms.
;
(assert (forall ((x U))
  (=> (or (= x e) (= x c))
      (axiom3 x))))

;
; Instantiated \neg \varphi on ground terms
;
(assert (forall ((x U))
  (=> (or (= x e) (= x c))
      (neg_varphi x))))

; Check satisfiability
(check-sat)