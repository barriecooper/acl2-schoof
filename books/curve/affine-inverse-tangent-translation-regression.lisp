(in-package "GFIELD")

(include-book "affine-inverse-tangent-translation")

; Client-facing regression: no relation definition or classifier is unfolded.
(defthm affine-inverse-tangent-translation-client-regression
  (implies
   (and (affine-opposite-y-infinity-relation-p p q infinity)
        (affine-doubling-relation-p q witness result))
   (or (affine-distinct-x-secant-relation-p
        p result (field-neg witness) q)
       (affine-doubling-relation-p p (field-neg witness) q)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance affine-inverse-tangent-translation
                     (a p) (b q) (infinity infinity)
                     (tangent witness) (u result)))
    :in-theory (theory 'minimal-theory))))
