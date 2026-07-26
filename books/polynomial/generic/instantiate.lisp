(in-package "GPOLY")

; Generate the ordinary executable definitions shared by the abstract theory
; and its concrete instances.  The expansion is deliberately just a PROGN of
; four DEFUN events: :TRANS1 makes every generated definition inspectable.
(defmacro def-normalize-eval-instance
  (fix-coefficients trim-trailing-zeros normalize eval
                    field-fix field-zero field-add field-mul)
  `(progn
     (defun ,fix-coefficients (xs)
       (if (atom xs) nil
         (cons (,field-fix (car xs))
               (,fix-coefficients (cdr xs)))))
     (defun ,trim-trailing-zeros (xs)
       (if (atom xs) nil
         (let ((tail (,trim-trailing-zeros (cdr xs))))
           (if (and (equal (,field-fix (car xs)) (,field-zero))
                    (endp tail))
               nil
             (cons (car xs) tail)))))
     (defun ,normalize (xs)
       (,trim-trailing-zeros (,fix-coefficients xs)))
     (defun ,eval (poly x)
       (if (atom poly)
           (,field-zero)
         (,field-add
          (,field-fix (car poly))
          (,field-mul (,field-fix x)
                      (,eval (cdr poly) x)))))))

; Addition is separate from negation/subtraction because an adapter may expose
; only the former.  Both macros expand solely to ordinary DEFUN events.
(defmacro def-add-instance
  (raw-add poly-add fix-coefficients normalize field-add)
  `(progn
     (defun ,raw-add (x y)
       (cond ((atom x) (,fix-coefficients y))
             ((atom y) (,fix-coefficients x))
             (t (cons (,field-add (car x) (car y))
                      (,raw-add (cdr x) (cdr y))))))
     (defun ,poly-add (x y)
       (,normalize
        (,raw-add (,normalize x) (,normalize y))))))

(defmacro def-neg-sub-instance
  (raw-neg poly-neg poly-sub poly-add normalize field-neg)
  `(progn
     (defun ,raw-neg (x)
       (if (atom x) nil
         (cons (,field-neg (car x)) (,raw-neg (cdr x)))))
     (defun ,poly-neg (x)
       (,normalize (,raw-neg (,normalize x))))
     (defun ,poly-sub (x y)
       (,poly-add x (,poly-neg y)))))

; Scalar multiplication has its own deliberately small generator.  Like the
; other generators above, its expansion contains ordinary DEFUN events only.
(defmacro def-scale-instance
  (raw-scale poly-scale normalize field-fix field-mul)
  `(progn
     (defun ,raw-scale (a x)
       (if (atom x) nil
         (cons (,field-mul (,field-fix a) (,field-fix (car x)))
               (,raw-scale a (cdr x)))))
     (defun ,poly-scale (a x)
       (,normalize (,raw-scale (,field-fix a) (,normalize x))))))

; Dense multiplication uses the constant-first Horner decomposition
; (a . f)g = a*g + X(f*g).  Only raw operations occur in the recursion;
; normalization is performed once, by the public operation.
(defmacro def-mul-instance
  (raw-mul poly-mul raw-add raw-scale normalize field-zero)
  `(progn
     (defun ,raw-mul (x y)
       (if (or (atom x) (atom y))
           nil
         (,raw-add (,raw-scale (car x) y)
                   (cons (,field-zero) (,raw-mul (cdr x) y)))))
     (defun ,poly-mul (x y)
       (,normalize (,raw-mul (,normalize x) (,normalize y))))))

; A deliberately narrow generator for concrete reduced-ring instances.  Every
; public name, generic source, rule class, and functional substitution is
; supplied by the caller.  Each supported theorem has an independent selector;
; a NIL theorem name omits just that theorem.  The expansion contains only
; ordinary DEFUN, VERIFY-GUARDS, and (when selected) DEFTHM events.
(defmacro def-reduced-ring-instance
  (reduced-add reduced-neg reduced-sub reduced-mul reduced-one
               poly-add poly-neg poly-sub poly-mul polynomial-one remainder
               mul-right-distributive-name mul-right-distributive-source
               functional-substitution common-goal-hints theorem-hints
               theorem-rule-classes
               &optional
               add-commutative-name add-commutative-source
               add-commutative-rule-classes add-commutative-hints
               add-associative-name add-associative-source
               add-associative-rule-classes add-associative-hints
               add-zero-left-name add-zero-left-source
               add-zero-left-rule-classes add-zero-left-hints
               add-zero-right-name add-zero-right-source
               add-zero-right-rule-classes add-zero-right-hints
               add-inverse-left-name add-inverse-left-source
               add-inverse-left-rule-classes add-inverse-left-hints
               add-inverse-right-name add-inverse-right-source
               add-inverse-right-rule-classes add-inverse-right-hints
               reduced-neg-double-name reduced-neg-double-source
               reduced-neg-double-rule-classes reduced-neg-double-hints
               reduced-neg-zero-name reduced-neg-zero-source
               reduced-neg-zero-rule-classes reduced-neg-zero-hints
               reduced-sub-self-name reduced-sub-self-source
               reduced-sub-self-rule-classes reduced-sub-self-hints
               reduced-sub-zero-right-name reduced-sub-zero-right-source
               reduced-sub-zero-right-rule-classes reduced-sub-zero-right-hints
               reduced-sub-zero-left-name reduced-sub-zero-left-source
               reduced-sub-zero-left-rule-classes reduced-sub-zero-left-hints
               reduced-sub-as-add-neg-name reduced-sub-as-add-neg-source
               reduced-sub-as-add-neg-rule-classes reduced-sub-as-add-neg-hints)
  `(progn
     (defun ,reduced-add (left right modulus)
       (,remainder (,poly-add left right) modulus))
     (defun ,reduced-neg (polynomial modulus)
       (,remainder (,poly-neg polynomial) modulus))
     (defun ,reduced-sub (left right modulus)
       (,remainder (,poly-sub left right) modulus))
     (defun ,reduced-mul (left right modulus)
       (,remainder (,poly-mul left right) modulus))
     (defun ,reduced-one (modulus)
       (,remainder (,polynomial-one) modulus))
     (verify-guards ,reduced-add)
     (verify-guards ,reduced-neg)
     (verify-guards ,reduced-sub)
     (verify-guards ,reduced-mul)
     (verify-guards ,reduced-one)
     ,@(and add-commutative-name
            `((defthm ,add-commutative-name
                (equal (,reduced-add a b modulus)
                       (,reduced-add b a modulus))
                :rule-classes ,add-commutative-rule-classes
                :hints
                (("Goal"
                  ,@common-goal-hints
                  :use ((:instance
                         (:functional-instance
                          ,add-commutative-source
                          ,@functional-substitution))))
                 ,@theorem-hints
                 ,@add-commutative-hints))))
     ,@(and add-associative-name
            `((defthm ,add-associative-name
                (equal
                 (,reduced-add (,reduced-add a b modulus) c modulus)
                 (,reduced-add a (,reduced-add b c modulus) modulus))
                :rule-classes ,add-associative-rule-classes
                :hints
                (("Goal"
                  ,@common-goal-hints
                  :use ((:instance
                         (:functional-instance
                          ,add-associative-source
                          ,@functional-substitution))))
                 ,@theorem-hints
                 ,@add-associative-hints))))
     ,@(and add-zero-left-name
            `((defthm ,add-zero-left-name
                (equal (,reduced-add nil first modulus)
                       (,remainder first modulus))
                :rule-classes ,add-zero-left-rule-classes
                :hints
                (("Goal"
                  ,@common-goal-hints
                  :use ((:instance
                         (:functional-instance
                          ,add-zero-left-source
                          ,@functional-substitution)
                         (a first))))
                 ,@theorem-hints
                 ,@add-zero-left-hints))))
     ,@(and add-zero-right-name
            `((defthm ,add-zero-right-name
                (equal (,reduced-add first nil modulus)
                       (,remainder first modulus))
                :rule-classes ,add-zero-right-rule-classes
                :hints
                (("Goal"
                  ,@common-goal-hints
                  :use ((:instance
                         (:functional-instance
                          ,add-zero-right-source
                          ,@functional-substitution)
                         (a first))))
                 ,@theorem-hints
                 ,@add-zero-right-hints))))
     ,@(and add-inverse-left-name
            `((defthm ,add-inverse-left-name
                (equal
                 (,reduced-add (,reduced-neg a modulus) a modulus)
                 nil)
                :rule-classes ,add-inverse-left-rule-classes
                :hints
                (("Goal"
                  ,@common-goal-hints
                  :use ((:instance
                         (:functional-instance
                          ,add-inverse-left-source
                          ,@functional-substitution))))
                 ,@theorem-hints
                 ,@add-inverse-left-hints))))
     ,@(and add-inverse-right-name
            `((defthm ,add-inverse-right-name
                (equal
                 (,reduced-add a (,reduced-neg a modulus) modulus)
                 nil)
                :rule-classes ,add-inverse-right-rule-classes
                :hints
                (("Goal"
                  ,@common-goal-hints
                  :use ((:instance
                         (:functional-instance
                          ,add-inverse-right-source
                          ,@functional-substitution))))
                 ,@theorem-hints
                 ,@add-inverse-right-hints))))
     ,@(and reduced-neg-double-name
            `((defthm ,reduced-neg-double-name
                (equal
                 (,reduced-neg (,reduced-neg a modulus) modulus)
                 (,remainder a modulus))
                :rule-classes ,reduced-neg-double-rule-classes
                :hints
                (("Goal"
                  ,@common-goal-hints
                  :use ((:instance
                         (:functional-instance
                          ,reduced-neg-double-source
                          ,@functional-substitution))))
                 ,@theorem-hints
                 ,@reduced-neg-double-hints))))
     ,@(and reduced-neg-zero-name
            `((defthm ,reduced-neg-zero-name
                (equal (,reduced-neg nil modulus) nil)
                :rule-classes ,reduced-neg-zero-rule-classes
                :hints
                (("Goal"
                  ,@common-goal-hints
                  :use ((:instance
                         (:functional-instance
                          ,reduced-neg-zero-source
                          ,@functional-substitution))))
                 ,@theorem-hints
                 ,@reduced-neg-zero-hints))))
     ,@(and reduced-sub-self-name
            `((defthm ,reduced-sub-self-name
                (equal (,reduced-sub a a modulus) nil)
                :rule-classes ,reduced-sub-self-rule-classes
                :hints
                (("Goal"
                  ,@common-goal-hints
                  :use ((:instance
                         (:functional-instance
                          ,reduced-sub-self-source
                          ,@functional-substitution))))
                 ,@theorem-hints
                 ,@reduced-sub-self-hints))))
     ,@(and reduced-sub-zero-right-name
            `((defthm ,reduced-sub-zero-right-name
                (equal (,reduced-sub a nil modulus)
                       (,remainder a modulus))
                :rule-classes ,reduced-sub-zero-right-rule-classes
                :hints
                (("Goal"
                  ,@common-goal-hints
                  :use ((:instance
                         (:functional-instance
                          ,reduced-sub-zero-right-source
                          ,@functional-substitution))))
                 ,@theorem-hints
                 ,@reduced-sub-zero-right-hints))))
     ,@(and reduced-sub-zero-left-name
            `((defthm ,reduced-sub-zero-left-name
                (equal (,reduced-sub nil a modulus)
                       (,reduced-neg a modulus))
                :rule-classes ,reduced-sub-zero-left-rule-classes
                :hints
                (("Goal"
                  ,@common-goal-hints
                  :use ((:instance
                         (:functional-instance
                          ,reduced-sub-zero-left-source
                          ,@functional-substitution))))
                 ,@theorem-hints
                 ,@reduced-sub-zero-left-hints))))
     ,@(and reduced-sub-as-add-neg-name
            `((defthm ,reduced-sub-as-add-neg-name
                (equal (,reduced-sub a b modulus)
                       (,reduced-add
                        a (,reduced-neg b modulus) modulus))
                :rule-classes ,reduced-sub-as-add-neg-rule-classes
                :hints
                (("Goal"
                  ,@common-goal-hints
                  :use ((:instance
                         (:functional-instance
                          ,reduced-sub-as-add-neg-source
                          ,@functional-substitution))))
                 ,@theorem-hints
                 ,@reduced-sub-as-add-neg-hints))))
     ,@(and mul-right-distributive-name
            `((defthm ,mul-right-distributive-name
                (equal
                 (,reduced-mul
                  (,reduced-add first second modulus) third modulus)
                 (,reduced-add
                  (,reduced-mul first third modulus)
                  (,reduced-mul second third modulus)
                  modulus))
                :rule-classes ,theorem-rule-classes
                :hints
                (("Goal"
                  ,@common-goal-hints
                  :use ((:instance
                         (:functional-instance
                          ,mul-right-distributive-source
                          ,@functional-substitution)
                         (a first) (b second) (c third))))
                 ,@theorem-hints))))))

; The coefficient-field embedding is intentionally its own tiny generator.
; Its expansion is one ordinary DEFUN, not a general algebra-instance layer.
(defmacro def-const-instance (const field-fix field-zero)
  `(defun ,const (a)
     (let ((fixed-a (,field-fix a)))
       (if (equal fixed-a (,field-zero))
           nil
         (list fixed-a)))))

; Degree and leading coefficient share one deliberately narrow, transparent
; generator.  Its expansion is exactly two ordinary DEFUN events.  Each
; public operation normalizes its arbitrary input once before inspecting the
; resulting canonical coefficient list.
(defmacro def-degree-instance (degree leading-coefficient normalize field-zero)
  `(progn
     (defun ,degree (poly)
       (let ((p (,normalize poly)))
         (if (consp p) (1- (len p)) -1)))
     (defun ,leading-coefficient (poly)
       (let ((p (,normalize poly)))
         (if (consp p) (car (last p)) (,field-zero))))))

; Monic normalization is a total, nonrecursive operation.  Its explicit zero
; branch avoids assigning mathematical significance to the total inverse of
; zero supplied by a field instance.
(defmacro def-monic-normalize-instance
  (monic-normalize normalize poly-scale leading-coefficient field-inv)
  `(defun ,monic-normalize (poly)
     (declare (xargs :guard t))
     (if (consp (,normalize poly))
         (,poly-scale (,field-inv (,leading-coefficient poly)) poly)
       nil)))


; Monomial/shift construction is shared by the generic theory and instances.
; The expansion contains exactly three ordinary DEFUN events.
(defmacro def-monomial-instance
  (zero-prefix poly-shift monomial normalize field-fix field-zero)
  `(progn
     (defun ,zero-prefix (n xs)
       (if (zp (nfix n)) xs
         (cons (,field-zero) (,zero-prefix (1- (nfix n)) xs))))
     (defun ,poly-shift (p n)
       (let ((p (,normalize p)))
         (if (consp p) (,zero-prefix (nfix n) p) nil)))
     (defun ,monomial (a n)
       (let ((a (,field-fix a)))
         (if (equal a (,field-zero)) nil
           (,zero-prefix (nfix n) (list a)))))))

; One leading-term cancellation, including its public normalization boundary
; and transparent result accessors.  The expansion is four ordinary DEFUNs:
; the core, public wrapper, term accessor, and next accessor.
(defmacro def-division-step-instance
  (core step term next degree leading monomial poly-sub poly-mul normalize
        field-div)
  `(progn
     (defun ,core (remainder divisor)
       (if (and (consp remainder) (consp divisor)
                (<= (,degree divisor) (,degree remainder)))
           (let* ((k (- (,degree remainder) (,degree divisor)))
                  (c (,field-div (,leading remainder) (,leading divisor)))
                  (term (,monomial c k)))
             (cons term (,poly-sub remainder (,poly-mul term divisor))))
         (cons nil remainder)))
     (defun ,step (remainder divisor)
       (let ((remainder (,normalize remainder))
             (divisor (,normalize divisor)))
         (,core remainder divisor)))
     (defun ,term (remainder divisor) (car (,step remainder divisor)))
     (defun ,next (remainder divisor) (cdr (,step remainder divisor)))))

; Canonical-state recursive division.  The length of the canonical remainder
; is the measure; each active iteration computes and reuses exactly one step.
(defmacro def-divmod-instance
  (core divmod canonical degree step-core poly-add normalize termination-theorem)
  `(progn
     (defun ,core (quotient remainder divisor)
       (declare
        (xargs :measure (len remainder)
               :hints (("Goal" :use ((:instance ,termination-theorem))
                        :in-theory (disable ,step-core)))))
       (if (and (,canonical quotient) (,canonical remainder)
                (,canonical divisor) (consp remainder) (consp divisor)
                (<= (,degree divisor) (,degree remainder)))
           (let* ((step (,step-core remainder divisor))
                  (term (car step))
                  (next (cdr step)))
             (,core (,poly-add quotient term) next divisor))
         (cons quotient remainder)))
     (defun ,divmod (f g)
       (let ((f (,normalize f)) (g (,normalize g)))
         (let ((result (,core nil f g)))
           (mv (car result) (cdr result)))))))

; Public projections deliberately call DIVMOD once and contain no recursion.
(defmacro def-divmod-projections-instance (quotient remainder divmod)
  `(progn
     (defun ,quotient (f g)
       (mv-let (q r) (,divmod f g)
         (declare (ignore r))
         q))
     (defun ,remainder (f g)
       (mv-let (q r) (,divmod f g)
         (declare (ignore q))
         r))))

; Divisibility and Euclidean gcd are kept in two small generators so the raw
; recursion and its monic post-processing remain separately inspectable.
(defmacro def-divisibility-instance (divides common-divisor remainder)
  `(progn
     (defun ,divides (divisor dividend)
       (declare (xargs :guard t))
       (equal (,remainder dividend divisor) nil))
     (defun ,common-divisor (candidate first second)
       (declare (xargs :guard t))
       (and (,divides candidate first)
            (,divides candidate second)))))

(defmacro def-euclidean-gcd-instance
  (euclidean-gcd monic-euclidean-gcd normalize remainder monic-normalize
                 termination-theorem)
  `(progn
     (defun ,euclidean-gcd (first second)
       (declare
        (xargs
         :measure (len (,normalize second))
         :hints (("Goal"
                  :use ((:instance ,termination-theorem
                                   (dividend first) (modulus second)))
                  :in-theory (disable ,normalize ,remainder)))))
       (if (consp (,normalize second))
           (,euclidean-gcd second (,remainder first second))
         (,normalize first)))
     (defun ,monic-euclidean-gcd (first second)
       (,monic-normalize (,euclidean-gcd first second)))))
