; fn: the remote consumer's listener -- its `[remote_consumer]' table
; (D48 / PKT-673; specs/applications.md "Remote consumer").
;
;   [remote_consumer]
;   port = 1563            ; required: no port, no listener
;   host = "127.0.0.1"     ; one listener address (the [listener] grammar)
;   max_sessions = 4       ; sessions at once; each draws its connection
;                          ; vector (books/consumer-remote-operation-source)
;
; TLS is not optional: FNCR authenticates an account's password, so the
; listener serves only with [listener]'s certificate and key.  The plan is
;   (:remote PORT FAMILY ADDRESS MAX-SESSIONS), (:none) or (:refused REASON).
(in-package "ACL2")
(include-book "native-config")
(include-book "consumer-remote-operation-source")

(defconst *fn-crc-default-host* "127.0.0.1")
(defconst *fn-crc-default-sessions* 4)

; The profile's key/value rows, as books/native-config.lisp parses them
; (books/web-config.lisp fn-web-config-pairs reads its table the same way).
(defun fn-crc-config-pairs (octets)
  (declare (xargs :guard t))
  (if (and (fn-ncfg-ascii-octetsp octets) (<= (len octets) *fn-ncfg-max-octets*))
      (let ((lines (fn-ncfg-lines octets)))
        (if (< *fn-ncfg-max-lines* (len lines)) :bad (fn-ncfg-parse-lines lines nil nil nil)))
    :bad))

(defun fn-crc-config-plan (octets listener-port tls-port certp)
  (declare (xargs :guard t))
  (let ((pairs (fn-crc-config-pairs octets)))
    (if (equal pairs :bad)
        (list :refused :syntax)
      (let* ((port (fn-ncfg-nat-value (fn-ncfg-value pairs "remote_consumer" "port") nil 65535))
             (web-port (fn-ncfg-nat-value (fn-ncfg-value pairs "web" "port") nil 65535))
             (host (fn-ncfg-string-value (fn-ncfg-value pairs "remote_consumer" "host")
                                         *fn-crc-default-host* *fn-ncfg-max-text* nil))
             (max (fn-ncfg-nat-value (fn-ncfg-value pairs "remote_consumer" "max_sessions")
                                     *fn-crc-default-sessions* *fn-crf-max-sessions*))
             (address (and (stringp host)
                           (fn-native-config-listener-address (fn-record-string-octets host)))))
        (cond ((null port) (list :none))
              ((or (equal port :bad) (equal port 0)) (list :refused :port))
              ((or (equal port listener-port) (equal port tls-port) (equal port web-port))
               (list :refused :port-taken))
              ((or (equal address :bad) (not (consp address))
                   (not (member (fn-ncfg-first address) '(:inet :inet6))))
               (list :refused :host))
              ((not certp) (list :refused :tls-needs-certificate))
              ((or (equal max :bad) (equal max 0)) (list :refused :bounds))
              (t (list :remote port (fn-ncfg-first address) (fn-ncfg-second address) max)))))))

(local
 (defthm fn-crc-nat-value-range
   (let ((v (fn-ncfg-nat-value value default ceiling)))
     (implies (and (natp default) (<= default ceiling) (not (equal v :bad)))
              (and (natp v) (<= v ceiling))))
   :hints (("Goal" :in-theory (enable fn-ncfg-nat-value fn-ncfg-second)))))

; The listener serves only beside [listener]'s certificate, and its session
; count is a positive number no larger than the class's ceiling.
(defthm fn-crc-plan-serves-only-with-a-certificate
  (implies (equal (car (fn-crc-config-plan octets listener-port tls-port certp)) :remote)
           (and certp
                (posp (nth 4 (fn-crc-config-plan octets listener-port tls-port certp)))
                (<= (nth 4 (fn-crc-config-plan octets listener-port tls-port certp))
                    *fn-crf-max-sessions*)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-crc-nat-value-range
                          (value (fn-ncfg-value (fn-crc-config-pairs octets)
                                                "remote_consumer" "max_sessions"))
                          (default *fn-crc-default-sessions*)
                          (ceiling *fn-crf-max-sessions*)))
           :in-theory (e/d (fn-crc-config-plan)
                           (fn-crc-config-pairs fn-ncfg-nat-value fn-ncfg-value
                            fn-ncfg-string-value fn-native-config-listener-address
                            fn-record-string-octets)))))

; -----------------------------------------------------------------------------
; The client's argv grammar (`fn consumer-remote ...', host/native/consumer-remote.lisp):
;   OP HOST PORT TRUST LOGIN SECRET-FILE, then
;     poll      NAME CURSOR-OUT REPORT-OUT
;     wait      NAME CURSOR-OUT REPORT-OUT SECONDS
;     ack       CURSOR-IN
;     position  NAME CURSOR-OUT
;     status    NAME
; TRUST is the PEM file of the anchor the node's certificate chains to.
; The plan is (:run OP HOST PORT TRUST LOGIN SECRET-FILE ARG OUT1 OUT2 SECONDS)
; with absent fields nil, or (:usage).
(defun fn-crc-cli-op (word)
  (declare (xargs :guard t))
  (cond ((equal word '(112 111 108 108)) :poll)                 ; poll
        ((equal word '(119 97 105 116)) :wait)                  ; wait
        ((equal word '(97 99 107)) :ack)                        ; ack
        ((equal word '(112 111 115 105 116 105 111 110)) :position) ; position
        ((equal word '(115 116 97 116 117 115)) :status)        ; status
        (t nil)))

(defun fn-crc-cli-wordp (word)
  (declare (xargs :guard t))
  (and (consp word) (fn-cbor-octet-listp word) (<= (len word) 512)))

(defun fn-crc-cli-wordsp (words)
  (declare (xargs :guard t))
  (if (consp words)
      (and (fn-crc-cli-wordp (car words)) (fn-crc-cli-wordsp (cdr words)))
    (null words)))

(defthm fn-crc-cli-wordsp-is-true-listp
  (implies (fn-crc-cli-wordsp words) (true-listp words))
  :rule-classes :forward-chaining)

(defun fn-crc-cli-plan (argv)
  (declare (xargs :guard t))
  (if (not (and (fn-crc-cli-wordsp argv) (<= 7 (len argv)) (<= (len argv) 10)))
      (list :usage)
    (let* ((op (fn-crc-cli-op (nth 0 argv)))
           (port (fn-ncfg-decimal (nth 2 argv)))
           (rest (nthcdr 6 argv))
           (n (len rest)))
      (if (not (and op (natp port) (< 0 port) (< port 65536)
                    (fn-frame-textp (nth 4 argv))))
          (list :usage)
        (let ((head (list :run op (nth 1 argv) port (nth 3 argv) (nth 4 argv) (nth 5 argv))))
          (case op
            (:poll (if (equal n 3) (append head (list (nth 0 rest) (nth 1 rest) (nth 2 rest) 0))
                     (list :usage)))
            (:wait (let ((seconds (and (equal n 4) (fn-ncfg-decimal (nth 3 rest)))))
                     (if (fn-cwait-secondsp seconds)
                         (append head (list (nth 0 rest) (nth 1 rest) (nth 2 rest) seconds))
                       (list :usage))))
            (:ack (if (equal n 1) (append head (list (nth 0 rest) nil nil 0)) (list :usage)))
            (:position (if (equal n 2) (append head (list (nth 0 rest) (nth 1 rest) nil 0))
                         (list :usage)))
            (otherwise (if (equal n 1) (append head (list (nth 0 rest) nil nil 0))
                         (list :usage)))))))))

; The local reply shape a remote operation answers with: the client reads it
; with the local consumer client's own reader (fn-native-control-host-consumer-client-read).
(defun fn-crc-local-operation (op)
  (declare (xargs :guard t))
  (case op
    (:poll :bound-poll) (:wait :bound-wait) (:ack :bound-ack)
    (:position :position) (otherwise :status)))
