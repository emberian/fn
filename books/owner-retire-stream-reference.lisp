; Proof-only denotation of the actual one-octet report cursor.
; None of these folds are host-called or allocation authority.
(in-package "ACL2")
(include-book "owner-retire-stream")

(defun fn-orr-peer-output (feeds)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp feeds)
      (append (fn-orf-nls-reference (fn-orr-peer-fields (car feeds)))
              (fn-orr-peer-output (cdr feeds)))
    nil))

(defun fn-orr-cached-total (feeds)
  (declare (xargs :guard t))
  (if (consp feeds)
      (+ (nfix (fn-feed-undelivered (fn-own-feed-entry-feed (car feeds))))
         (fn-orr-cached-total (cdr feeds)))
    0))

(defun fn-orr-obligation-output (pins)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp pins)
      (append (fn-orf-nls-reference (fn-orr-obligation-fields (car pins)))
              (fn-orr-obligation-output (cdr pins)))
    nil))

(defun fn-orr-postscript (outcome u held)
  (declare (xargs :guard (and (natp u) (natp held)) :verify-guards nil))
  (append (fn-orf-nls-reference (fn-ord-end (equal outcome :drained) u held))
          (if (and (zp u) (zp held)) nil
            (fn-orf-nls-reference (fn-ord-release)))))

(defun fn-orr-tail-denotation (phase feeds pins root u held reserved outcome)
  (declare (xargs :guard (and (natp u) (natp held) (natp reserved))
                  :verify-guards nil))
  (case phase
    (:count-pins
     (append (fn-orr-peer-output feeds)
             (fn-orf-nls-reference (fn-ord-header (+ held (len pins)) reserved))
             (fn-orr-obligation-output root)
             (fn-orr-postscript outcome (+ u (fn-orr-cached-total feeds))
                                (+ held (len pins)))))
    (:peers
     (append (fn-orr-peer-output feeds)
             (fn-orf-nls-reference (fn-ord-header held reserved))
             (fn-orr-obligation-output pins)
             (fn-orr-postscript outcome (+ u (fn-orr-cached-total feeds)) held)))
    (:obligations (append (fn-orr-obligation-output pins)
                          (fn-orr-postscript outcome u held)))
    (:release (if (and (zp u) (zp held)) nil
                (fn-orf-nls-reference (fn-ord-release))))
    (otherwise nil)))

(defun fn-orr-denotation (cursor)
  (declare (xargs :guard (fn-orr-invariant cursor) :verify-guards nil))
  (let ((phase (nth 0 cursor)) (feeds (nth 1 cursor)) (pins (nth 2 cursor))
        (root (nth 3 cursor)) (u (nth 4 cursor)) (held (nth 5 cursor))
        (reserved (nth 6 cursor)) (outcome (nth 7 cursor)))
    (if (equal phase :emit)
        (append (fn-orf-denotation (nth 8 cursor))
                (fn-orr-tail-denotation (nth 9 cursor) feeds pins root u held reserved outcome))
      (fn-orr-tail-denotation phase feeds pins root u held reserved outcome))))

(local
 (defthm fn-orr-append-associative
   (equal (append (append a b) c) (append a (append b c)))))

(defthm fn-orr-emitter-start-reference
  (implies (fn-orf-fieldsp fields)
           (equal (fn-orf-denotation (fn-orf-start fields))
                  (fn-orf-nls-reference fields)))
  :hints (("Goal" :in-theory (disable fn-orf-denotation fn-orf-start
                                     fn-orf-reference fn-orf-nls-reference))))

(defthm fn-orr-step-conserves-denotation
  (implies (fn-orr-invariant cursor)
           (equal (append (mv-nth 1 (fn-orr-step cursor))
                          (fn-orr-denotation (mv-nth 0 (fn-orr-step cursor))))
                  (fn-orr-denotation cursor)))
  :hints (("Goal"
           :use ((:instance fn-orf-step-conserves-denotation (c (nth 8 cursor)))
                 (:instance fn-orf-step-done-is-terminal (c (nth 8 cursor)))
                 (:instance fn-orf-terminal-denotation
                            (c (mv-nth 0 (fn-orf-step (nth 8 cursor))))))
           :in-theory
           (e/d (fn-orr-step fn-orr-denotation fn-orr-tail-denotation
                 fn-orr-postscript fn-orr-cursor fn-orr-schedule fn-orr-invariant
                 fn-orr-peer-output fn-orr-obligation-output fn-orr-cached-total)
                (fn-orf-step fn-orf-denotation fn-orf-start fn-orf-reference
                 fn-orf-nls-reference fn-orf-invariant fn-orf-terminalp
                 fn-orr-peer-fields fn-orr-obligation-fields fn-ord-header fn-ord-end
                 fn-ord-release fn-orf-step-conserves-denotation
                 fn-orf-step-done-is-terminal fn-orf-terminal-denotation)))))

(defthm fn-orr-final-denotation-by-definition
  (implies (equal (nth 0 cursor) :done)
           (equal (fn-orr-denotation cursor) nil))
  :hints (("Goal" :in-theory (enable fn-orr-denotation fn-orr-tail-denotation))))

(defthm fn-orr-step-final-conservation
  (implies (and (fn-orr-invariant cursor) (mv-nth 2 (fn-orr-step cursor)))
           (equal (mv-nth 1 (fn-orr-step cursor)) (fn-orr-denotation cursor)))
  :hints (("Goal"
           :use ((:instance fn-orr-step-conserves-denotation)
                 (:instance fn-orr-step-done-is-final)
                 (:instance fn-orr-final-denotation-by-definition
                            (cursor (mv-nth 0 (fn-orr-step cursor)))))
           :in-theory (disable fn-orr-step fn-orr-invariant fn-orr-denotation
                               fn-orr-step-conserves-denotation fn-orr-step-done-is-final
                               fn-orr-final-denotation-by-definition mv-nth))))

(defthm fn-orr-run-is-complete-denotation
  (implies (fn-orr-invariant cursor)
           (equal (fn-orr-run cursor) (fn-orr-denotation cursor)))
  :hints (("Goal" :induct (fn-orr-run cursor)
           :in-theory (disable fn-orr-step fn-orr-invariant fn-orr-denotation mv-nth))))

(defun fn-orr-feed-domainp (feeds)
  (declare (xargs :guard t))
  (if (consp feeds)
      (and (fn-feed-count-relationp (fn-own-feed-entry-feed (car feeds)))
           (fn-orr-feed-domainp (cdr feeds)))
    t))

(defun fn-orr-pins-domainp (pins)
  (declare (xargs :guard t))
  (if (consp pins)
      (and (fn-orr-pin-domainp (car pins)) (fn-orr-pins-domainp (cdr pins)))
    t))

(defthm fn-orr-peer-output-is-actual-reference
  (implies (fn-orr-feed-domainp feeds)
           (equal (fn-orr-peer-output feeds) (fn-oret-peer-lines feeds)))
  :hints (("Goal" :induct (fn-orr-peer-output feeds)
           :in-theory (e/d (fn-orr-peer-output fn-orr-feed-domainp fn-oret-peer-lines)
                           (fn-orr-peer-fields fn-orf-nls-reference fn-orr-peer-line
                            fn-oret-peer-line fn-feed-count-relationp)))))

(defthm fn-orr-cached-total-is-actual-reference
  (implies (fn-orr-feed-domainp feeds)
           (equal (fn-orr-cached-total feeds) (fn-oret-undelivered-total feeds)))
  :hints (("Goal" :induct (fn-orr-cached-total feeds)
           :in-theory (enable fn-orr-cached-total fn-orr-feed-domainp
                              fn-feed-count-relationp fn-oret-undelivered-total))))

(defthm fn-orr-obligation-output-is-actual-reference
  (implies (fn-orr-pins-domainp pins)
           (equal (fn-orr-obligation-output pins) (fn-nls-obligation-lines pins)))
  :hints (("Goal" :induct (fn-orr-obligation-output pins)
           :in-theory (e/d (fn-orr-obligation-output fn-orr-pins-domainp fn-nls-obligation-lines)
                           (fn-orr-obligation-fields fn-orf-nls-reference
                            fn-nls-obligation-line fn-orr-pin-domainp)))))

(defthm fn-orr-header-reference
  (implies (and (natp held) (natp reserved))
           (equal (fn-orf-nls-reference (fn-ord-header held reserved))
                  (append (fn-nls-text "obligations=") (fn-nls-nat held)
                          (fn-nls-field "reserved" reserved) *fn-nls-lf*)))
  :hints (("Goal" :in-theory (e/d (fn-orf-nls-reference fn-ord-header
                                     fn-nls-field fn-nls-value)
                                  (fn-nls-nat fn-nls-text)))))

(defthm fn-orr-postscript-is-actual-end-line
  (implies (and (natp u) (natp held))
           (equal (fn-orr-postscript outcome u held) (fn-orr-end-line outcome u held)))
  :hints (("Goal" :in-theory (e/d (fn-orr-postscript fn-orr-end-line
                                     fn-orf-nls-reference fn-ord-end fn-ord-release
                                     fn-oret-outcome-word fn-nls-field fn-nls-value)
                                  (fn-nls-nat fn-nls-text)))))

(defun fn-orr-report-domainp (oc)
  (declare (xargs :guard t))
  (let* ((o (fn-ocfg-owner oc))
         (retention (fn-nls-retention (fn-own-store o))))
    (and (fn-orr-feed-domainp (fn-own-feeds o))
         (fn-orr-pins-domainp (fn-retain-pins retention))
         (natp (fn-retain-reserved retention)))))

(defthm fn-orr-start-denotation-is-actual-report
  (implies (fn-orr-report-domainp oc)
           (equal (fn-orr-denotation (fn-orr-start outcome oc))
                  (fn-oret-report outcome oc)))
  :hints (("Goal"
           :in-theory
           (e/d (fn-orr-report-domainp fn-orr-start fn-orr-denotation
                 fn-orr-tail-denotation fn-oret-report fn-oret-obligation-words
                 fn-orr-end-line)
                (fn-orr-peer-output fn-orr-cached-total fn-orr-obligation-output
                 fn-orf-nls-reference fn-ord-header fn-orr-postscript
                 fn-oret-peer-lines fn-oret-undelivered-total fn-nls-obligation-lines
                 fn-nls-field fn-nls-nat fn-nls-text fn-oret-outcome-word)))))

(defthm fn-orr-complete-output-is-actual-report
  (implies (fn-orr-report-domainp oc)
           (equal (fn-orr-run (fn-orr-start outcome oc))
                  (fn-oret-report outcome oc)))
  :hints (("Goal" :in-theory (disable fn-orr-run fn-orr-start fn-orr-denotation
                                     fn-orr-report-domainp fn-oret-report))))

(verify-guards fn-orr-peer-output
  :hints (("Goal" :in-theory (disable fn-orr-peer-fields fn-orf-fieldsp fn-orf-nls-reference))))
(verify-guards fn-orr-obligation-output
  :hints (("Goal" :in-theory (disable fn-orr-obligation-fields fn-orf-fieldsp fn-orf-nls-reference))))
(verify-guards fn-orr-postscript
  :hints (("Goal" :in-theory (disable fn-ord-end fn-ord-release fn-orf-fieldsp fn-orf-nls-reference))))
(verify-guards fn-orr-tail-denotation
  :hints (("Goal" :in-theory (disable fn-ord-header fn-ord-release fn-orf-fieldsp fn-orf-nls-reference
                                     fn-orr-peer-output fn-orr-obligation-output
                                     fn-orr-postscript fn-orr-cached-total))))
(verify-guards fn-orr-denotation
  :hints (("Goal" :in-theory (enable fn-orr-invariant))))
