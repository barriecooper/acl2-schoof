(in-package "HS")
(include-book "eval")

; The zero polynomial has degree -1.
(defun poly-degree (poly)
  (if (endp poly) -1 (1- (len poly))))

(defthm degree-normalize-bound
  (<= (poly-degree (poly-normalize poly)) (poly-degree poly))
  :rule-classes :linear)
