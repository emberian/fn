; Shared authority completion/recovery interpreter MODEL/source teeth.
; No native allocator/sidecar publication claim; candidate refusal is pure
; preflight whose actual pre-allocation collector remains a composition debt.
(in-package "ACL2")
(include-book "../../books/consumer-authority-fold")
(include-book "control-visible-effect-tests")

(defconst *caat-32* (make-list 32 :initial-element 9))
(defconst *caat-16* (make-list 16 :initial-element 8))
(defconst *caat-initial* (fn-cp-state *caat-32* *caat-32* 0 1 nil))

(defun fn-caat-event (s txid op)
  (list :consumer-authority (fn-cp-nth 3 s) txid 0 op))
(defun fn-caat-row-op (candidate base login birth digest)
  (list :authority-row candidate base login birth *caat-32* *caat-16*
        digest *caat-32* *caat-32* 1))
(defun fn-caat-next (s txid op)
  (fn-cp-nth 1 (fn-caa-step s (fn-caat-event s txid op))))
(defun fn-caat-seal (s txid)
  (let ((p (fn-cp-nth 5 (fn-cp-nth 6 s))))
    (fn-caat-next s txid (list :authority-seal (fn-cp-nth 1 p)
                               (fn-cp-nth 2 p) (fn-cp-nth 3 p) (fn-cp-nth 7 p)))))
(defun fn-caat-fence (s txid)
  (let ((p (fn-cp-nth 5 (fn-cp-nth 6 s))))
    (fn-caa-step s (fn-caat-event s txid
                   (list :authority-fence (fn-cp-nth 1 p) (fn-cp-nth 2 p)
                         (fn-cp-nth 3 p) (fn-cp-nth 7 p))))))

(defconst *caat-begin-event*
  (fn-caat-event *caat-initial* 1 '(:authority-begin (65) 0 1 7)))
(defconst *caat-begun* (fn-cp-nth 1 (fn-caa-step *caat-initial* *caat-begin-event*)))
(defconst *caat-row-event*
  (fn-caat-event *caat-begun* 2 (fn-caat-row-op '(65) 0 '(97) 2 *caat-32*)))
(defconst *caat-staged* (fn-cp-nth 1 (fn-caa-step *caat-begun* *caat-row-event*)))
(defconst *caat-sealed* (fn-caat-seal *caat-staged* 3))
(defconst *caat-ready* (fn-caat-next *caat-sealed* 4 '(:authority-prepare (65) 0)))
(defconst *caat-committed* (fn-caat-fence *caat-ready* 5))
(defconst *caat-first* (fn-cp-nth 1 *caat-committed*))
(defconst *caat-root* (fn-cp-nth 2 *caat-committed*))
(defconst *caat-token* (fn-cp-nth 2 (car (fn-cp-nth 4 (fn-cp-nth 6 *caat-first*)))))


(defconst *carft-fence-event*
  (let ((p (fn-cp-nth 5 (fn-cp-nth 6 *caat-ready*))))
    (fn-caat-event *caat-ready* 5
      (list :authority-fence (fn-cp-nth 1 p) (fn-cp-nth 2 p)
            (fn-cp-nth 3 p) (fn-cp-nth 7 p)))))
(defconst *carft-seal-event*
  (let ((p (fn-cp-nth 5 (fn-cp-nth 6 *caat-staged*))))
    (fn-caat-event *caat-staged* 3
      (list :authority-seal (fn-cp-nth 1 p) (fn-cp-nth 2 p)
            (fn-cp-nth 3 p) (fn-cp-nth 7 p)))))
(defconst *carft-prep-event*
  (fn-caat-event *caat-sealed* 4 '(:authority-prepare (65) 0)))
(defconst *carft-history*
  (list *caat-begin-event* *caat-row-event* *carft-seal-event*
        *carft-prep-event* *carft-fence-event*))

; Full publication root and persisted fence event-count survive the SAME
; validated decision, while generic old projection refuses authority tags.
(assert-event
 (let ((one (fn-carf-event-step *caat-ready* *carft-fence-event* 4 :unknown)))
   (and (fn-cac-eventp *carft-fence-event*)
        (fn-store-event-p *carft-fence-event*)
        (fn-wire-event-p *carft-fence-event*)
        (equal (fn-cpe-projection-step *caat-ready* *carft-fence-event* 4)
               '(:refused :authority-interpreter-required))
        (equal one (list :ok *caat-first* *caat-root* 5))
        (equal (fn-store-event-decode-exact (fn-store-event-encode *carft-fence-event*))
               (list :ok *carft-fence-event*))
        (equal (fn-carf-fold nil *carft-history* nil *caat-initial* nil nil 0 0)
               one))))

; Ordinary plain/verified article effect preserves authority literally.
(assert-event
 (and (fn-cp-statep *caat-first*)
      (equal (fn-carf-effect-step *caat-first* :preserved) (list :ok *caat-first*))
      (equal (fn-cp-nth 6 (fn-cp-nth 1 (fn-carf-effect-step *caat-first* :changed)))
             (fn-cp-nth 6 (fn-cp-nth 1 (fn-carv-semantic-step *caat-first*))))))

(defun carft-candidate (cp candidate new old verdicts old-verdicts hist)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-hist
    (mv-let (ans fn-hist)
      (let* ((fn-hist (fn-hist-load (true-list-fix hist) 0 fn-hist))
             (files (fn-sf-make :idle 6 nil hist nil nil nil nil)))
        (mv (mv-list 3 (fn-carf-append-candidate-step
                        cp candidate (fn-cp-nth 3 cp) new old nil old
                        old-verdicts verdicts files fn-hist nil)) fn-hist))
      ans)))
(defconst *carft-cancel*
  (cvit-rec 5 6 "<c2@example.invalid>" '("control.cancel") *cvit-c2-bytes*))
(defconst *carft-exhausted*
  (fn-carv-revision-state *caat-first* *fn-cbor-max-uint*))

; Exhaustion on a core-derived verified author cancel refuses the pure
; candidate BEFORE any allocator call; no proposed CP/root is returned.
; Actual host/native collector ordering and capture freshness are still OPEN.
(assert-event
 (let ((one (carft-candidate *carft-exhausted* *carft-cancel*
                             (list *cvit-c2* *cvit-t*) (list *cvit-t*)
                             *cvit-v1* (cdr *cvit-v1*) (list *cvit-rt*))))
   (and (fn-cp-statep *carft-exhausted*)
        (fn-cp-nth 3 (fn-cp-nth 6 *carft-exhausted*))
        (equal (fn-cp-nth 1 (fn-cp-nth 6 *carft-exhausted*)) *fn-cbor-max-uint*)
        (fn-held-p *carft-cancel*)
        (equal (fn-store-event-sequence *carft-cancel*)
               (fn-cp-nth 3 *carft-exhausted*))
        (fn-ctl-withdrawalp (car (cadr one)))
        (equal (car one) '(:refused :authority-revision-exhausted)))))

; A same-txid configuration precedes the fence and discards pending adoption.
; Replaying only the authority substream would incorrectly publish it.
(defconst *carft-config*
  (fn-cfg-record-make 0 5 1 (list (fn-cfg-set-capacity 20)) *fn-cfg-default-stamp*))
(assert-event
 (and (fn-cfg-recordp *carft-config*)
      (fn-cpr-config-firstp (list *carft-config*) (list *carft-fence-event*))
      (eq (car (fn-carf-fold nil *carft-history* nil *caat-initial* nil nil 0 0)) :ok)
      (not (eq (car (fn-carf-fold (list *carft-config*) *carft-history* nil
                                  *caat-initial* nil nil 0 0)) :ok))))

; Hypothesis removal: retain exhausted revision but there is no active
; namespace yet, so the same change aborts preparation without revision wrap.
(assert-event
 (let ((s (fn-carv-revision-state *caat-initial* *fn-cbor-max-uint*)))
   (and (fn-cp-statep s) (not (fn-cp-nth 3 (fn-cp-nth 6 s)))
        (equal (fn-cp-nth 1 (fn-cp-nth 6 s)) *fn-cbor-max-uint*)
        (not (equal (fn-carf-effect-step s :changed)
                    '(:refused :authority-revision-exhausted))))))

; Hypothesis removal: retain active namespace, but revision is not exhausted.
(assert-event
 (and (fn-cp-statep *caat-first*) (fn-cp-nth 3 (fn-cp-nth 6 *caat-first*))
      (not (equal (fn-cp-nth 1 (fn-cp-nth 6 *caat-first*)) *fn-cbor-max-uint*))
      (not (equal (fn-carf-effect-step *caat-first* :changed)
                  '(:refused :authority-revision-exhausted)))))
