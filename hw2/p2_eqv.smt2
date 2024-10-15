; Declare the boolean variables.
(declare-const p Bool)
(declare-const q Bool)
(declare-const r Bool)

; Defining the original formula phi.
(define-const origina_formula Bool
(and
    (or q (not r))
    (or (not p) r)
    (or (not q) r p)
    (or p q (not q))
    (or (not r) q)
)
)

; Defining the new formula psi with the implied clauses added.
(define-const new_formula Bool
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
; the original formula does not match the new_formula.
; If this is unsatisfiable, it means that the formulas
; are equivalent (as there are no valuations of {p, q, r}
; for which the formulas do not match).
(assert (not (= origina_formula new_formula)))

; Check satisfiability.
(check-sat)