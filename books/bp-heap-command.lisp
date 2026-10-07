; BP served launcher projection. This does not admit a complete BP command;
; it identifies the Store owner/connection profile for the pre-entry reservation.
(in-package "ACL2")
(include-book "bp-session-profile")
(include-book "heap-reservation")
(include-book "heap-store-figure")
(include-book "profile-limits")

(defun fn-bph-decimal-characters (chars value)
 (declare (xargs :guard (and (true-listp chars) (natp value))))
 (if (endp chars) value
  (let ((c (car chars)))
   (if (and (characterp c) (<= (char-code #\0) (char-code c))
            (<= (char-code c) (char-code #\9)))
    (fn-bph-decimal-characters (cdr chars)
                              (+ (* 10 value) (- (char-code c) (char-code #\0))))
    nil))))
(defun fn-bph-connections (text)
 (declare (xargs :guard t))
 ;; A concurrency profile integer is represented by the existing u64 format.
 ;; Check the string length before materializing its characters. This is a
 ;; bounded input grammar, not a stored-data or retained-history ceiling.
 (if (and (stringp text) (<= 1 (length text)) (<= (length text) 20))
  (let ((n (fn-bph-decimal-characters (coerce text 'list) 0)))
   (and (posp n) (< n 18446744073709551616) n))
  nil))

(defun fn-bph-command-plan (argv)
 (declare (xargs :guard (true-listp argv)))
 (let* ((node (and (equal (nth 0 argv) "bp-node")
                  (equal (nth 1 argv) "serve")))
        (app (and (equal (nth 0 argv) "bp-app")
                 (equal (nth 1 argv) "receive")))
        (root (nth 4 argv)))
  (cond ((not (or node app)) '(:not-served-bp))
        ((not (and (stringp root) (< 0 (length root)))) '(:refused :store-root))
        ((and node (not (consp (nthcdr 13 argv)))) '(:refused :node-arguments))
        ((and app (not (consp (nthcdr 12 argv)))) '(:refused :app-arguments))
        (t (let ((connections (if node 1 (fn-bph-connections (nth 12 argv)))))
             (if (posp connections) (list :run root connections)
              '(:refused :connections)))))))

(defun fn-bph-refusal-line (reason)
 (declare (xargs :guard t))
 (cond ((equal reason :store-root) "BP served command requires a Store root")
       ((equal reason :node-arguments) "BP node serve requires its complete required arguments")
       ((equal reason :app-arguments) "BP app receive requires its complete required arguments")
       ((equal reason :connections) "BP app owner connections must be a positive u64 decimal")
       ((equal reason :transfer-mru) "BP node transfer MRU must be a positive u64 decimal")
       (t "BP served command reservation is malformed")))

(defthm fn-bph-connections-representable
 (implies (fn-bph-connections text)
  (and (posp (fn-bph-connections text))
       (< (fn-bph-connections text) 18446744073709551616))))
(defthm fn-bph-command-plan-owns-exact-served-root
 (implies (equal (car (fn-bph-command-plan argv)) :run)
  (and (equal (cadr (fn-bph-command-plan argv)) (nth 4 argv))
       (stringp (nth 4 argv))
       (< 0 (length (nth 4 argv)))
       (or (and (equal (nth 0 argv) "bp-node") (equal (nth 1 argv) "serve")
                (equal (caddr (fn-bph-command-plan argv)) 1))
           (and (equal (nth 0 argv) "bp-app") (equal (nth 1 argv) "receive")
                (equal (caddr (fn-bph-command-plan argv))
                       (fn-bph-connections (nth 12 argv)))))))
 :rule-classes nil)

; ---------------------------------------------------------------------------
; A BP node's heap counts its BP terms.  The node's startup check
; (fn-bpsp-node-startup, books/bp-session-profile.lisp) demands the store figure
; plus fn-bpsp-node-capacity from the dynamic space; the launcher's probe grows
; the store's reservation by that same figure.  The host observes the two profiles
; under the journal root and the transfer MRU and decides nothing.

; `bp-node serve' arguments the node reads before and after an optional trailing
; `--control-config CONFIG' pair: JOURNAL is argument 3, the transfer MRU argument 18.
(defun fn-bph-before-control (argv)
 (declare (xargs :guard (true-listp argv)))
 (cond ((endp argv) nil)
       ((equal (car argv) "--control-config") nil)
       (t (cons (car argv) (fn-bph-before-control (cdr argv))))))
(defun fn-bph-node-serve-p (argv)
 (declare (xargs :guard (true-listp argv)))
 (and (equal (nth 0 argv) "bp-node") (equal (nth 1 argv) "serve")
      (equal (car (fn-bph-command-plan argv)) :run)))
(defun fn-bph-node-journal (argv)
 (declare (xargs :guard (true-listp argv)))
 (nth 3 (fn-bph-before-control argv)))
; The transfer MRU: DEFAULT when the argument is absent, else its u64 decimal
; (NIL when malformed).
(defun fn-bph-node-transfer (argv default)
 (declare (xargs :guard (true-listp argv)))
 (let ((text (nth 18 (fn-bph-before-control argv))))
  (if text (fn-bph-connections text) default)))

; TERMS: NIL (not a BP node serve), else (SESSION-PROFILE NODE-PROFILE
; TRANSFER-MRU SEGMENT-MRU), the values fnn-bp-session-install is given.
(defun fn-bph-extend-reservation (base terms0 core observations)
 (declare (xargs :guard t))
 (let ((terms (true-list-fix terms0)) (base0 base) (base (true-list-fix base)))
 (cond ((not terms0) base0)
       ((not (equal (car base) :heap)) base0)
       (t
        (let ((need (fn-bpsp-node-capacity (nth 0 terms) (nth 1 terms) (nth 2 terms) (nth 3 terms))))
         (if (not need)
             (list :refused :invalid-bp-session-terms 0 (nth 3 base))
          (let* ((mb (fn-heap-mb-of
                      (fn-heap-grow-runtime-dynamic (* *fn-heap-mib* (nfix (nth 1 base))) need
                         (* *fn-heap-mib* (fn-profile-limit :gc-nursery-mib)))))
                 (stack (nfix (nth 4 base)))
                 (threads (nfix (nth 5 base)))
                 (total (fn-heap-reservation-octets mb core stack threads)))
           (if (<= total (fn-heap-machine-octets observations))
               (list :heap mb (nth 2 base) (nth 3 base) stack threads)
             (list :refused :machine-cannot-hold-threads (fn-heap-mb-of total) (nth 3 base))))))))))

; The premise the keystone below names, discharged for the probe's own base: the
; :run reservation's megabytes cover the store figure (fn-heap-figure-octets of
; the profile, the core and the nursery) the node recomputes at its startup.
(defthm fn-bph-reserve-of-keeps-the-decision-mb
 (implies (and (fn-bs-profile-admittedp profile) (natp (nth 1 d)) (equal (car (fn-heap-reserve-of d profile core observations connections)) :heap))
          (equal (nth 1 (fn-heap-reserve-of d profile core observations connections)) (nth 1 d)))
 :hints (("Goal" :in-theory (e/d (fn-heap-reserve-of fn-heap-reserve-storeless fn-heap-decision-mb)
                                 (fn-heap-figure-octets fn-heap-mb-of fn-heap-machine-octets
                                  fn-heap-reservation-octets)))))
(defthm fn-bph-decision-mb-natp-covers-the-figure
 (implies (and (fn-bs-profile-admittedp profile)
               (equal (car (fn-heap-decide profile core nursery observations)) :heap))
          (and (natp (nth 1 (fn-heap-decide profile core nursery observations)))
               (<= (fn-heap-figure-octets profile core nursery)
                   (* *fn-heap-mib* (nth 1 (fn-heap-decide profile core nursery observations))))))
 :hints (("Goal" :in-theory (union-theories '(car-cons cdr-cons nth-0-cons nth-add1 (:executable-counterpart equal) (:executable-counterpart nfix) (:executable-counterpart not) fn-heap-figure-octets nfix natp (:type-prescription fn-heap-mb-of-natp) (:type-prescription fn-heap-store-figure-octets-natp)) (theory 'minimal-theory))
          :expand ((fn-heap-decide profile core nursery observations))
          :use ((:instance fn-heap-mb-of-covers (octets (fn-heap-figure-octets profile core nursery)))))))
(defthm fn-bph-run-reservation-covers-the-store-figure
 (implies (and (fn-bs-profile-admittedp profile)
               (equal (car (fn-heap-reserve-operation-decide :run profile core nursery observations connections nil)) :heap))
          (<= (fn-heap-figure-octets profile core nursery)
              (* *fn-heap-mib* (nth 1 (fn-heap-reserve-operation-decide :run profile core nursery observations connections nil)))))
 :hints (("Goal" :in-theory (union-theories '((:executable-counterpart member-equal) (:executable-counterpart equal)) (theory 'minimal-theory))
          :use ((:instance fn-heap-reserve-operation-decide-of-a-serve-action (action :run))
                (:instance fn-heap-reserve-decide-is-reserve-of-heap-decide)
                (:instance fn-bph-reserve-of-keeps-the-decision-mb
                  (d (fn-heap-decide profile core nursery observations)))
                (:instance fn-heap-reserve-of-holds-the-decision
                  (d (fn-heap-decide profile core nursery observations)))
                (:instance fn-bph-decision-mb-natp-covers-the-figure)))))

; KEYSTONE: a reservation the extension accepts is a dynamic space in which the
; node's own startup check holds its sessions, never refusing the capacity.  BASE
; is the probe's store decision (its megabytes cover STORE-NEED, the store figure
; the node recomputes: fn-heap-decide); the same terms the host reads for
; the install are the terms the extension was given.
(defthm fn-bph-extended-reservation-holds-bp-sessions
 (implies (and (equal (car base) :heap) (natp store-need)
               (<= store-need (* *fn-heap-mib* (nfix (nth 1 base))))
               (equal (car (fn-bph-extend-reservation base (list profile node transfer segment)
                                                      core observations))
                      :heap))
          (equal (car (fn-bpsp-node-startup profile node transfer segment
                       (* *fn-heap-mib*
                          (nth 1 (fn-bph-extend-reservation base (list profile node transfer segment)
                                                            core observations)))
                       store-need))
                 :hold))
 :hints (("Goal" :in-theory (e/d (fn-bph-extend-reservation)
                                 (fn-bpsp-node-capacity fn-bpsp-node-startup fn-heap-mb-of
                                  fn-heap-reservation-octets fn-heap-machine-octets))
          :use ((:instance fn-bpsp-node-startup-holds-the-capacity
                  (dynamic (* *fn-heap-mib*
                              (nth 1 (fn-bph-extend-reservation base (list profile node transfer segment)
                                                                core observations)))))
                (:instance fn-heap-mb-of-covers
                  (octets (fn-heap-grow-runtime-dynamic
                           (* *fn-heap-mib* (nfix (nth 1 base)))
                           (fn-bpsp-node-capacity profile node transfer segment)
                           (* *fn-heap-mib* (fn-profile-limit :gc-nursery-mib)))))
                (:instance fn-heap-grow-runtime-dynamic-covers-addition
                  (dynamic (* *fn-heap-mib* (nfix (nth 1 base))))
                  (extra (fn-bpsp-node-capacity profile node transfer segment))
                  (nursery-cap (* *fn-heap-mib* (fn-profile-limit :gc-nursery-mib))))))))
