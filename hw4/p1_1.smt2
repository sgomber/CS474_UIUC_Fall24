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
(assert (axiom1 e e c))
(assert (axiom1 e e e))
(assert (axiom1 e c c))
(assert (axiom1 e c e))
(assert (axiom1 c e c))
(assert (axiom1 c e e))
(assert (axiom1 c c c))
(assert (axiom1 c c e))

;
; Instantiated Axiom 2 on ground terms.
;
(assert (axiom2 e))
(assert (axiom2 c))

;
; Instantiated Axiom 3 on ground terms.
;
(assert (axiom3 e))
(assert (axiom3 c))

;
; Instantiated \neg \varphi on ground terms
;
(assert (neg_varphi e))
(assert (neg_varphi c))

; Check satisfiability
(check-sat)