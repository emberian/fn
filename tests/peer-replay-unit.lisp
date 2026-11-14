; Concrete inbound peer replay contract. Runs the composed served core through
; fn2-cursor-wire-run (adapter simulator), not fn2-pm-* or the wire reference.
; Same-node, one live connection, successful simulated durable I/O; no claim
; about reconnect/lost replies, real disk, peer honesty, catchup or custody.
(in-package "ACL2")
(include-book "../books/owed-cursor")
(include-book "../sim/check-wire")

(defun fn2-peer-replay-block (mid body)
  (declare (xargs :verify-guards nil))
  (list (fn2-csp-cat (list "TAKETHIS " mid))
        "Path: peer!not-for-mail" "From: peer@example.invalid"
        "Subject: peer replay" "Date: Fri, 30 Oct 2026 12:00:00 +0000"
        "Newsgroups: local.test" (fn2-csp-cat (list "Message-ID: " mid))
        "" body "."))

(defun fn2-peer-replay-lines (fresh)
  (declare (xargs :verify-guards nil))
  (append '("MODE STREAM" "CHECK <replay@example.invalid>")
          (fn2-peer-replay-block "<replay@example.invalid>" "original body")
          (fn2-peer-replay-block "<replay@example.invalid>" "original body")
          (fn2-peer-replay-block (if fresh "<fresh@example.invalid>" "<replay@example.invalid>")
                                "conflicting body")
          '("CHECK <replay@example.invalid>" "IHAVE <replay@example.invalid>"
            "GROUP local.test" "BODY 1" "QUIT")))

(defun fn2-peer-replay-expected (fresh)
  (declare (xargs :verify-guards nil))
  (list (fn2-cw-crlf-octets
         (append '("200 fn-nntp experimental server ready" "203 streaming permitted"
                   "238 <replay@example.invalid>" "239 <replay@example.invalid>"
                   "439 <replay@example.invalid>")
                 (list (if fresh "239 <fresh@example.invalid>" "439 <replay@example.invalid>"))
                 '("438 <replay@example.invalid>" "435 duplicate")
                 (list (if fresh "211 2 1 2 local.test" "211 1 1 1 local.test"))
                 '("222 1 <replay@example.invalid> body follows" "original body" "."
                   "205 closing connection")))
        t))

(defun fn2-peer-replay-check (fresh chunk)
  (declare (xargs :verify-guards nil))
  (let* ((bytes (fn2-cw-crlf-octets (fn2-peer-replay-lines fresh)))
         (sizes (and (posp chunk)
                     (make-list (+ 1 (floor (len bytes) chunk)) :initial-element chunk)))
         (r (fn2-cursor-wire-run
              (put-assoc-equal :peering-interim t *fn2-cursor-profile*) nil
              (list (list bytes sizes t))))
         (want (fn2-peer-replay-expected fresh)))
    (and (equal (nth 0 r) :ok)
         (equal (nth 1 r) :quiet)
         (equal (nth 3 r) 0)
         (or (equal (car (nth 2 r)) want)
             (cw "peer replay fresh=~x0 got ~x1 expected ~x2~%" fresh (car (nth 2 r)) want)))))

; Positive: both duplicate and conflicting identity leave body/count/high intact.
(assert-event (fn2-peer-replay-check nil nil))
; Exercise framing across short reads, including command/header delimiters.
(assert-event (fn2-peer-replay-check nil 7))
; Independent control: changing the conflicting transfer's Message-ID admits
; it and increases the number/high-water. An implementation rejecting all
; follow-up transfers cannot satisfy this same wire/count observation.
(assert-event (fn2-peer-replay-check t nil))
