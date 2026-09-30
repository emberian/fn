; Constructed completion-shape witnesses. These are not a persisted accept
; or native lifecycle qualification; SCN-1046 supplies that composed subject.
(in-package "ACL2")
(include-book "../../books/owner-outcome-counted")
(defconst *oct-agent* (fn-record-string-octets "a.fn.test"))
(defconst *oct-config*
  (fn-inj-make-config t *oct-agent* (list (fn-record-string-octets "fn.letters")) 32768))
(defconst *oct-peer*
  (fn-cfg-peer-make "p" "p.fn.test" '(:nntp "127.0.0.1" 1120)
                    '("fn.*" 32768 16) '("fn.*" t 256 1000)
                    '(:source-address "127.0.0.2")))
(defconst *oct-table* (fn-own-feed-install-one "p" (fn-cfg-peer-rows *oct-peer*) nil))
(defconst *oct-wire*
  (append (fn-record-string-octets "From: poster@example.invalid") '(13 10)
          (fn-record-string-octets "Subject: exact") '(13 10)
          (fn-record-string-octets "Newsgroups: fn.letters") '(13 10)
          (fn-record-string-octets "Message-ID: <count@example.invalid>") '(13 10 13 10)
          (fn-record-string-octets "Body.") '(13 10)))
(defconst *oct-decision*
  (fn-own-control-decision *oct-config* (fn-record-string-octets "<count@example.invalid>")
                           (list (fn-record-string-octets "fn.letters")) *oct-wire*))
(defconst *oct-owner*
  (fn-own-make nil nil nil 1 4 nil '(committed) nil nil *oct-config* nil
               (fn-own-sub-make :control 0 0 *oct-decision*) *oct-table* nil nil))
(defconst *oct-completed* (fn-oct-control *oct-owner* :durable 0))
(assert-event
 (and (fn-own-control-submissionp (fn-own-inflight *oct-owner*))
      (fn-own-completion-consumedp *oct-owner*)
      (equal 0 (fn-own-feed-table-pending-model (fn-own-feeds *oct-owner*)))
      (fn-ofct-table-relationp (fn-own-feeds *oct-owner*))
      (equal (fn-own-outcome-completion *oct-owner* :durable) :durable)
      (equal (car *oct-completed*) (fn-own-control-outcome *oct-owner* :durable))
      (equal (cdr *oct-completed*) 1)
      (equal (fn-own-feed-table-pending-model (fn-own-feeds (car *oct-completed*))) 1)
      (fn-ofct-table-relationp (fn-own-feeds (car *oct-completed*)))
      (not (fn-own-inflight (car *oct-completed*)))))
; Replaying completion on the retired submission must never enqueue twice.
(assert-event
 (equal (fn-oct-control (car *oct-completed*) :durable 1)
        (cons (car *oct-completed*) 1)))
