(in-package "ACL2")
(include-book "../../books/snapshot-row-source-remap")
(include-book "../../books/stx-keyring-records")
(defconst *osmt-binding*
 (fn-ab-make :native-source (append *fn-ab-subject-head* (make-list 32 :initial-element 0))))
(defconst *osmt-wire*
 (fn-record-make 0 0 0 "<one@example>" '(1 2 3) '("fn.test")
                 "p" "c" "r" 1 841000000 *osmt-binding*))
(defconst *osmt-held* (fn-held-plain *osmt-wire* 65536))
(defconst *osmt-keyring* (fn-stxk-make 7 6 1 7 '(116 101 115 116) '(1 2 3 4)))
; A shape-only composite wrapper checks shallow dispatch and statement
; borrowing here; cryptographic/accepted Store correspondence is separate.
(defconst *osmt-composite* (fn-hstxa-make :original-statement *osmt-held*))
(assert-event
 (and (fn-record-p *osmt-wire*) (fn-held-p *osmt-held*) (fn-stxk-p *osmt-keyring*)
      (mv-let (mapped next) (fn-osm-row-source (list :resident *osmt-keyring*) 0)
        (and (equal mapped (list :resident *osmt-keyring*)) (equal next 0)))
      (mv-let (mapped next) (fn-osm-row-source (list :resident *osmt-held*) 0)
        (and (equal next 1) (fn-held-p (cadr mapped))
             (equal (fn-held-payload (cadr mapped)) 0)
             (equal (fn-held-binding (cadr mapped)) *osmt-binding*)
             (equal (fn-orm-tail 5 (cadr mapped)) (fn-orm-tail 5 *osmt-held*))))
      (mv-let (mapped next) (fn-osm-row-source (list :resident *osmt-composite*) 1)
        (and (equal next 2)
             (equal (fn-hstxa-stxa (cadr mapped)) :original-statement)
             (equal (fn-held-payload (fn-hstxa-held (cadr mapped))) 1)
             (equal (fn-held-binding (fn-hstxa-held (cadr mapped))) *osmt-binding*)))))
; No duplicate offer or completion advances either counter.
(defconst *osmt-source* '(9 (12 2) 0 0))
(defconst *osmt-begin* (fn-osm-begin *osmt-source*))
(defconst *osmt-row* (list :row 0 (list :resident *osmt-held*) *osmt-source* :future))
(defconst *osmt-wait*
 (mv-let (word row cursor) (fn-osm-prepare-row *osmt-begin* *osmt-row*)
  (declare (ignore word row)) cursor))
(defconst *osmt-next*
 (mv-let (word cursor) (fn-osm-census-ack *osmt-wait* '(:need-row 2 1 8 nil (12 2) :resource))
  (declare (ignore word)) cursor))
(assert-event
 (and (equal (car *osmt-wait*) :waiting) (equal (nth 2 *osmt-wait*) 0)
      (equal (car *osmt-next*) :idle) (equal (nth 2 *osmt-next*) 1)
      (equal (nth 1 *osmt-next*) '(9 (12 2) 0 1))
      (mv-let (word row cursor) (fn-osm-prepare-row *osmt-wait* *osmt-row*)
       (declare (ignore row))
       (and (equal word '(:refused :remap-source)) (equal cursor *osmt-wait*)))
      (mv-let (word cursor) (fn-osm-census-ack *osmt-next* '(:need-row 2 1 8 nil (12 2) :resource))
       (and (equal word '(:refused :remap-census-ack)) (equal cursor *osmt-next*)))))
; Pass reset uses the same original source but begins target handle zero.
(assert-event
 (equal (fn-osm-begin '(9 (12 2) 1 0)) '(:idle (9 (12 2) 1 0) 0 nil)))

; The target handle can cross a codec scalar width: census must encode the
; mapped row, rather than carry the original encoded size.
(assert-event
 (mv-let (mapped next) (fn-osm-row-source (list :resident *osmt-held*) 0)
  (and (equal next 1)
       (< (len (fn-scc-program (cadr mapped)))
          (len (fn-scc-program *osmt-held*))))))
