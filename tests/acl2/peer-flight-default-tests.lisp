; Witnesses and generated teeth for books/peer-flight-default.lisp: the
; default peer flight profile `init' writes (catch-up out of the box).
(in-package "ACL2")
(include-book "../../books/peer-flight-default")
(include-book "../../books/defkeystone")

(defconst *pfdt-dev* *fn-bs-profile-development*)
(defconst *pfdt-scale* *fn-bs-profile-scale*)
; The development preset's default: the least heap, two spools, two
; flights, one worker, a spool of its record bound and the quantum, four
; units per history octet.
(assert-event
 (equal (fn-pfp-default-policy *pfdt-dev*)
        (list 11728 (* 2 (+ 17138486 262144)) 2 1 (+ 17138486 262144) (* 4 25165824))))
(assert-event (fn-pfr-policy-p (fn-pfp-default-policy *pfdt-scale*)))
(assert-event (equal (len (fn-pfp-default-octets *pfdt-dev*)) 52))
; Not a store profile at all: still a policy (the clamps), the least spool.
(assert-event (equal (fn-pfp-default-policy :garbage) (list 11728 524288 2 1 262144 0)))

; A run reservation the probe extends (BASE), a core observation, and three
; machines: one that holds BASE and the default's extra, one that holds BASE
; alone (the probe refuses the default there), one of 16 octets.
(defconst *pfdt-base* (list :heap 1000 0 0 1024 36))
(defconst *pfdt-core* (cons 0 0))
(defconst *pfdt-big* (list 8000000000))
(defconst *pfdt-base-only* (list (fn-pfd-base-octets *pfdt-base* *pfdt-core*)))
(defconst *pfdt-tiny* (list 16))
(assert-event
 (and (equal (car (fn-pfr-extend-reservation *pfdt-base* (fn-pfp-default-policy *pfdt-dev*)
                                             *pfdt-core* *pfdt-big*))
             :heap)
      (equal (car (fn-pfr-extend-reservation *pfdt-base* (fn-pfp-default-policy *pfdt-dev*)
                                             *pfdt-core* *pfdt-base-only*))
             :refused)))
(defteeth fn-pfd-default-is-a-policy
  :claim (() (fn-pfr-policy-p (fn-pfp-default-policy values)))
  :subject fn-pfp-default-policy
  :witness ((values *pfdt-dev*))
  :breaks ()
  :mutations ((no-bookkeeping-heap
               (:conclusion (fn-pfr-policy-p (update-nth 0 0 (fn-pfp-default-policy values))))
               ((values *pfdt-dev*))
               :fault "a default whose heap does not hold its flights' bookkeeping")))

(defteeth fn-pfd-default-decodes-to-itself
  :claim (() (equal (fn-pfp-read t (fn-pfp-default-octets values))
                    (fn-pfp-default-policy values)))
  :subject fn-pfp-default-octets
  :witness ((values *pfdt-dev*))
  :breaks ()
  :mutations ((short-write
               (:conclusion (equal (fn-pfp-read t (cdr (fn-pfp-default-octets values)))
                                   (fn-pfp-default-policy values)))
               ((values *pfdt-dev*))
               :fault "a profile file one octet short (a torn write)")))

(defteeth fn-pfd-default-spools-one-batch
  :claim (() (<= (+ (nfix (fn-bs-profile-max-record-octets values)) *fn-cu-request-quantum*)
                 (fn-pfr-at 4 (fn-pfp-default-policy values))))
  :subject fn-pfp-default-policy
  :witness ((values *pfdt-dev*))
  :breaks ()
  :mutations ((record-ignored
               (:conclusion (<= (+ (nfix (fn-bs-profile-max-record-octets values))
                                   *fn-cu-request-quantum*)
                                (fn-pfd-spool 0)))
               ((values *pfdt-dev*))
               :fault "a spool sized to the quantum alone, ignoring the store's record bound")))

(defteeth fn-pfd-default-launches-where-its-extra-fits
  :claim (((heap-base (equal (fn-pfr-at 0 base) :heap))
           (fits (<= (+ (fn-pfd-base-octets base core)
                        (fn-pfd-launch-extra (fn-pfr-at 4 base)))
                     (fn-heap-machine-octets observations))))
          (equal (fn-pfr-at 0 (fn-pfr-extend-reservation
                               base (fn-pfp-default-policy values) core observations))
                 :heap))
  :subject fn-pfr-extend-reservation
  :witness ((base *pfdt-base*) (core *pfdt-core*) (observations *pfdt-big*) (values *pfdt-dev*))
  :breaks ((heap-base ((base (list :refused :machine-cannot-hold-profile 0 0 0 0))
                       (core *pfdt-core*) (observations *pfdt-big*) (values *pfdt-dev*)))
           (fits ((base *pfdt-base*) (core *pfdt-core*) (observations *pfdt-tiny*)
                  (values *pfdt-dev*))))
  :mutations ((base-only
               (:hypothesis fits (<= (fn-pfd-base-octets base core)
                                     (fn-heap-machine-octets observations)))
               ((base *pfdt-base*) (core *pfdt-core*) (observations *pfdt-base-only*)
                (values *pfdt-dev*))
               :fault "an init that reserves the store's run alone, without the default's launch extra")))
