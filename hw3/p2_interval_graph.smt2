; Ls and Us corresponding to our four nodes.
(declare-const L1 Real)
(declare-const U1 Real)
(declare-const L2 Real)
(declare-const U2 Real)
(declare-const L3 Real)
(declare-const U3 Real)
(declare-const L4 Real)
(declare-const U4 Real)

; Function to check if the interval [la, ua] is non-empty.
(define-fun nonempty ((la Real) (ua Real)) Bool
    (< la ua))

; Function to check if [la, ua] and [lb, ub] represent different intervals.
(define-fun unequal ((la Real) (ua Real) (lb Real) (ub Real)) Bool
    (not (and (= la ua) (= lb ub))))

; Function to check if [la, ua] and [lb, ub] intersect
(define-fun intersect ((la Real) (ua Real) (lb Real) (ub Real)) Bool
    (exists ((x Real)) (and (< la x) (< x ua) (< lb x) (< x ub))))


; Constraints to enforce that the intervals are non-empty.
(assert (nonempty L1 U1))
(assert (nonempty L2 U2))
(assert (nonempty L3 U3))
(assert (nonempty L4 U4))

; Constraints to encode that the intervals are different.
(assert (unequal L1 U1 L2 U2))
(assert (unequal L1 U1 L3 U3))
(assert (unequal L1 U1 L4 U4))
(assert (unequal L2 U2 L3 U3))
(assert (unequal L2 U2 L4 U4))
(assert (unequal L3 U3 L4 U4))

; Constraints to encode that the pair of intervals (i1,i2), (i1,i4), (i2,i3) and (i3,i4) intersect.
(assert (intersect L1 U1 L2 U2))
(assert (intersect L1 U1 L4 U4))
(assert (intersect L2 U2 L3 U3))
(assert (intersect L3 U3 L4 U4))

; Constraints to encode that the pair of intervals (i1,i3) and (i2,i4) don't intersect.
(assert (not (intersect L1 U1 L3 U3)))
(assert (not (intersect L2 U2 L4 U4)))

(check-sat)