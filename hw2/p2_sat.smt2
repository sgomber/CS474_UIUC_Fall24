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

; Assert phi and check satisfiability.
(assert phi)
(check-sat)

; Get the model.
(get-model)