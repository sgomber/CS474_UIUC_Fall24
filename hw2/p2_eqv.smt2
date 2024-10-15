; Declare the boolean variables.
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)

; Defining the original formula phi.
(define-const phi Bool
(and
    (or q (not r))
    (or (not p) r)
    (or (not q) r p)
    (or p q (not q))
    (or (not r) q)
)
)

; Defining the new formula psi with the implied clauses added.
(define-const psi Bool
(and
    (or q (not r))
    (or (not p) r)
    (or (not q) r p)
    (or p q (not q))
    (or (not r) q)

    ; New implied clauses
    (or (not q) r)
    (or (not p) q)
)
)

; Check if there is a valuation for {p, q, r} where
; the phi does not match psi.
; If this is unsatisfiable, it means that the formulas
; are equivalent (as there are no valuations of {p, q, r}
; for which the formulas do not match).
(assert (not (= phi psi)))

; Check satisfiability.
(check-sat)