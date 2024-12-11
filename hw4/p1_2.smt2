(set-logic UF)

(declare-sort U 0) ; Declare U as an uninterpreted sort

; Declare the functions and constants
(declare-fun f (U U) U)
(declare-fun g (U) U)
(declare-const e U)
(declare-const d1 U)
(declare-const d2 U)
(declare-const d3 U)

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
(define-fun neg_varphi () Bool
  (and (= (f d1 d2) e) (= (f d2 d1) e) (= (f d1 d3) e) (= (f d3 d1) e) (not (= d2 d3))))

;
; Instantiated Axiom 1 on ground terms.
;
(assert (forall ((x U) (y U) (z U))
  (=> (and (or (= x e) (= x d1) (= x d2) (= x d3))
           (or (= y e) (= y d1) (= y d2) (= y d3))
           (or (= z e) (= z d1) (= z d2) (= z d3)))
       (axiom1 x y z))))

;
; Instantiated Axiom 2 on ground terms.
;
(assert (forall ((x U))
  (=> (or (= x e) (= x d1) (= x d2) (= x d3))
      (axiom2 x))))

;
; Instantiated Axiom 3 on ground terms.
;
(assert (forall ((x U))
  (=> (or (= x e) (= x d1) (= x d2) (= x d3))
      (axiom3 x))))

;
; Instantiated \neg \varphi on ground terms (neg_varphi has no forall quantifiers)
;
(assert neg_varphi)

; Check satisfiability
(check-sat)