(set-logic UF)

(declare-sort U 0) ; Declare U as an uninterpreted sort

(declare-fun f (U U) U)
(declare-fun g (U) U)
(declare-const e U)
(declare-const c U)

;
; Instantiated formulas for Axiom 1
;
(assert (= (f (f e e) e) (f e (f e e))))
(assert (= (f (f e e) c) (f e (f e c))))
(assert (= (f (f e c) e) (f e (f c e))))
(assert (= (f (f e c) c) (f e (f c c))))
(assert (= (f (f c e) e) (f c (f e e))))
(assert (= (f (f c e) c) (f c (f e c))))
(assert (= (f (f c c) e) (f c (f c e))))
(assert (= (f (f c c) c) (f c (f c c))))

;
; Instantiated formulas for Axiom 2
;
(assert (and (= (f e e) e) (= (f e e) e)))
(assert (and (= (f c e) c) (= (f e c) c)))

;
; Instantiated formulas for Axiom 3
;
(assert (and (= (f e (g e)) e) (= (f (g e) e) e)))
(assert (and (= (f c (g c)) e) (= (f (g c) c) e)))

;
; Instantiated formulas for \neg \varphi
;
(assert (and (= (f e c) e) (= (f c e) e) (not (= e c))))
(assert (and (= (f c c) c) (= (f c c) c) (not (= e c))))

; Check satisfiability
(check-sat)