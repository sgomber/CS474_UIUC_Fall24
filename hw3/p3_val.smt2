(assert 
    (forall ((x Real)) 
            (exists ((y Real)) 
                    (and (> (* 2 y) (* 3 x)) (< (* 4 y) (+ (* 8 x) 10)))
            )
    )
)

(check-sat)