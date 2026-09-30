(in-package "ACL2")
(include-book "../../books/owner-recovery-canonical-census")
(defmacro rcct-begin (d ctx fields)
 `(mv-let (word source collector) (fn-rcc-begin ,d ,ctx ,fields nil :resource-ref)
   (list word source collector)))
(defmacro rcct-read (c source osm hct)
 `(mv-let (word payload next) (fn-rcc-readout ,c ,source ,osm ,hct)
   (list word payload next)))
; Internal scalar/model fixture, not an authenticated checkpoint/install.
(defconst *rcct-ctx* '(:ok 0 nil nil nil nil))
(defconst *rcct-fields*
 (list (fn-scs-summary :ok) (fn-scs-summary 0) (fn-scs-summary nil)
       (fn-scs-summary nil) (fn-scs-summary nil) (fn-scs-summary nil)))
(defconst *rcct-token* '(:recovery-source 7 3 2))
(defconst *rcct-descriptor*
 (list :recovery-census *rcct-token* 3 5 :borrowed-store-root nil 0 0 :borrowed-cp))
(defconst *rcct-start* (rcct-begin *rcct-descriptor* *rcct-ctx* *rcct-fields*))
; The actual empty source cursor takes its actual prefix -> suffix step.
(defconst *rcct-source*
 (fn-osrc-at 1 (fn-osrc-tick (cadr *rcct-start*) nil)))
(defconst *rcct-collector* (caddr *rcct-start*))
(assert-event
 (let* ((c *rcct-collector*) (osm (fn-omk-at 2 c)) (hct (fn-omk-at 3 c))
        (r (rcct-read c *rcct-source* osm hct)))
  (and (eq (car *rcct-start*) :census)
       (eq (car r) :measured)
       (equal (cadr r) (list :measured *rcct-token* 0 0 *rcct-ctx* *rcct-fields* nil))
       (eq (fn-omk-at 0 (caddr r)) :measured)
       (not (eq (car r) :ready))
       ; CP provenance is still absent; measurement does not manufacture it.
       (null (fn-omk-at 6 (caddr r))))))
(assert-event
 (let ((c *rcct-collector*))
  (equal (rcct-read c (cadr *rcct-start*) (fn-omk-at 2 c) (fn-omk-at 3 c))
         (list :pending nil c))))
; Completed output is consumed once; repeat does not re-run source or replace
; the retained terminal collector with a new counted state.
(assert-event
 (let* ((c *rcct-collector*) (osm (fn-omk-at 2 c)) (hct (fn-omk-at 3 c))
        (r (rcct-read c *rcct-source* osm hct)) (measured (caddr r)))
  (equal (rcct-read measured *rcct-source* osm hct) (list :pending nil measured))))
; Actual issuer-current scalar relation is necessary but is not auth/funds.
(assert-event
 (let ((issuer (list :recovering 7 3 nil 0 0 *rcct-ctx* 2 5)))
  (and (fn-rcc-currentp *rcct-collector* issuer 3 5)
       (not (fn-rcc-currentp *rcct-collector* issuer 4 5))
       (not (fn-rcc-currentp *rcct-collector* issuer 3 6))
       (not (fn-rcc-currentp *rcct-collector* (update-nth 7 3 issuer) 3 5)))))
; Corrupt capture pair cannot be offered as the current measured census.
(assert-event
 (let* ((c *rcct-collector*) (osm (fn-omk-at 2 c))
        (bad (update-nth 5 '(8 0) (fn-omk-at 3 c))))
  (equal (rcct-read c *rcct-source* osm bad) (list :pending nil c))))

; Configured Store frontier may advance beyond the suffix fold, as allowed
; by the actual readonly input getter. Current identity does not imply that
; the final seal has already observed that newer frontier.
(assert-event
 (let* ((issuer (list :recovering 7 3 nil 0 0 *rcct-ctx* 2 5))
        (advanced (update-nth 1 (update-nth 7 9 *rcct-descriptor*) *rcct-collector*))
        (ahead-issuer (update-nth 5 10 issuer)))
  (and (fn-rcc-currentp advanced issuer 3 5)
       (not (fn-rcc-currentp advanced ahead-issuer 3 5)))))
