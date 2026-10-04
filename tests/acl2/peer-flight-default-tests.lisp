; Witnesses and generated teeth for books/peer-flight-default.lisp: the
; default peer flight profile `init' writes, and the catch-up verb's
; admission on a node without one (catch-up out of the box).
(in-package "ACL2")
(include-book "../../books/peer-flight-default")
(include-book "../../books/defkeystone")
(include-book "../../books/native-admin")

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

; -----------------------------------------------------------------------------
; Step 3: the catch-up verb's admission, over the operator grammar's own plans.
(defun pfdt-argv (words)
  (if (consp words)
      (cons (fn-record-string-octets (car words)) (pfdt-argv (cdr words)))
    nil))
(defconst *pfdt-catch-up* (fn-native-admin-plan (pfdt-argv '("peer" "catch-up" "A" "2"))))
(defconst *pfdt-catch-up-stop* (fn-native-admin-plan (pfdt-argv '("peer" "catch-up" "A" "0"))))
(defconst *pfdt-pull* (fn-native-admin-plan (pfdt-argv '("peer" "pull" "A" "20"))))
(defconst *pfdt-funded* (fn-pfp-default-policy *pfdt-dev*))
(defconst *pfdt-refusal* (fn-native-admin-result :refused :catch-up-unfunded nil nil 0 nil nil))
; Each grammar plan is accepted; only the starting catch-up is observed.
(assert-event
 (and (equal (fn-native-admin-result-status *pfdt-catch-up*) :accepted)
      (equal (fn-native-admin-result-status *pfdt-catch-up-stop*) :accepted)
      (equal (fn-native-admin-result-status *pfdt-pull*) :accepted)
      (fn-pfp-catch-up-observes-p *pfdt-catch-up*)
      (not (fn-pfp-catch-up-observes-p *pfdt-catch-up-stop*))
      (not (fn-pfp-catch-up-observes-p *pfdt-pull*))))
; Unfunded (no file, or anything that is not a policy): refused by name.
; Funded: the plan itself.  `peer catch-up A 0' stops on any node.
(assert-event
 (and (equal (fn-pfp-catch-up-admission *pfdt-catch-up* nil) *pfdt-refusal*)
      (equal (fn-pfp-catch-up-admission *pfdt-catch-up* :bad) *pfdt-refusal*)
      (equal (fn-pfp-catch-up-admission *pfdt-catch-up* *pfdt-funded*) *pfdt-catch-up*)
      (equal (fn-pfp-catch-up-admission *pfdt-catch-up-stop* nil) *pfdt-catch-up-stop*)
      (equal (fn-pfp-catch-up-admission *pfdt-pull* nil) *pfdt-pull*)))

(defconst *pfdt-catch-up-argv* (pfdt-argv '("peer" "catch-up" "A" "2")))
(defteeth fn-pfp-catch-up-verb-accepted-only-funded
  :claim (((request (and (equal (car (fn-native-admin-words argv)) "peer")
                         (equal (cadr (fn-native-admin-words argv)) "catch-up")
                         (equal (len (fn-native-admin-words argv)) 4)))
           (accepted (equal (fn-native-admin-result-status (fn-native-admin-plan argv)) :accepted))
           (starts (posp (fn-native-admin-decimal-value
                          (coerce (cadddr (fn-native-admin-words argv)) 'list)))))
          (and (iff (equal (fn-native-admin-result-status
                            (fn-pfp-catch-up-admission (fn-native-admin-plan argv) observed))
                           :accepted)
                    (fn-pfr-policy-p observed))
               (implies (not (fn-pfr-policy-p observed))
                        (equal (fn-native-admin-result-reason
                                (fn-pfp-catch-up-admission (fn-native-admin-plan argv) observed))
                               :catch-up-unfunded))))
  :subject fn-pfp-catch-up-admission
  :witness ((argv *pfdt-catch-up-argv*) (observed nil))
  :breaks ((request ((argv (pfdt-argv '("peer" "pull" "A" "20"))) (observed nil)))
           (accepted ((argv (pfdt-argv '("peer" "catch-up" "" "2"))) (observed *pfdt-funded*)))
           (starts ((argv (pfdt-argv '("peer" "catch-up" "A" "0"))) (observed nil))))
  :mutations ((unfunded-accepted
               (:conclusion (equal (fn-native-admin-result-status
                                    (fn-pfp-catch-up-admission (fn-native-admin-plan argv) observed))
                                   :accepted))
               ((argv *pfdt-catch-up-argv*) (observed nil))
               :fault "the verb before step 3: catch-up accepted with no profile, every round then failing peer-flight-unfunded")))

(defteeth fn-pfp-catch-up-admission-is-identity-elsewhere
  :claim (((elsewhere (or (not (fn-pfp-catch-up-observes-p plan)) (fn-pfr-policy-p observed))))
          (equal (fn-pfp-catch-up-admission plan observed) plan))
  :subject fn-pfp-catch-up-admission
  :witness ((plan *pfdt-catch-up-stop*) (observed nil))
  :breaks ((elsewhere ((plan *pfdt-catch-up*) (observed nil))))
  :mutations ((observation-ignored
               (:conclusion (equal (fn-pfp-catch-up-admission plan nil) plan))
               ((plan *pfdt-catch-up*) (observed *pfdt-funded*))
               :fault "an admission that refuses catch-up whatever profile the host observed")))
