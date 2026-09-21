;;; Native acquisition seam for the external freshness anchor.
;;;
;;; Raw Lisp owns only OS entropy, DNS/UDP and cryptographic primitive
;;; observations.  ACL2 produces the request datagram, parses the response,
;;; reconstructs both signature subjects and later decides window, pinning,
;;; freshness, acceptance and persistence.  Endpoint/key selection is an
;;; injected result of the future pinned-server manifest; this file has no
;;; default server and no key table.

(in-package "ACL2")

(defconstant +fnn-anchor-nonce-octets+ 32)
(defconstant +fnn-anchor-request-octets+ 1024)
(defconstant +fnn-anchor-max-response-octets+ 4096)
(defconstant +fnn-anchor-max-host-octets+ 255)
(defconstant +fnn-anchor-max-timeout-seconds+ 60)

(defun fnn-anchor-valid-endpoint-p (host port timeout)
  (and (stringp host)
       (<= 1 (length host) +fnn-anchor-max-host-octets+)
       (integerp port) (<= 1 port 65535)
       (realp timeout) (< 0 timeout) (<= timeout +fnn-anchor-max-timeout-seconds+)))

(defun fnn-anchor-csprng-nonce ()
  "Read one nonce from the OS CSPRNG.  A short/failed device read is a fault."
  (let ((fd (fnn-open "/dev/urandom" sb-posix:o-rdonly))
        (answer (fnn-make-octets +fnn-anchor-nonce-octets+))
        (offset 0))
    (unwind-protect
         (progn
           (loop while (< offset +fnn-anchor-nonce-octets+) do
             (let* ((remaining (- +fnn-anchor-nonce-octets+ offset))
                    (chunk (fnn-make-octets remaining))
                    (count (fnn-read-fd fd chunk)))
               (when (zerop count)
                 (fnn-fault "OS CSPRNG ended before one nonce"))
               (replace answer chunk :start1 offset :end2 count)
               (incf offset count)))
           answer)
      (fnn-close fd))))

(defun fnn-anchor-request (nonce)
  "Ask ACL2 for the exact deployed NONC/PAD request and copy its octets."
  (let ((result (fnn-core 'fn-anchor-wire-host-request
                          (fnn-octet-list nonce))))
    (unless (and (listp result) (= (length result) 2)
                 (eq (first result) :request)
                 (fnn-octet-list-p (second result))
                 (= (length (second result)) +fnn-anchor-request-octets+))
      (fnn-fault "ACL2 returned an invalid anchor request"))
    (fnn-octets (second result))))

(defun fnn-anchor-resolve-v4 (host)
  "The bounded first IPv4 result.  The pinned manifest remains endpoint owner."
  (if (typep host '(simple-array (unsigned-byte 8) (4)))
      host
    (sb-bsd-sockets:host-ent-address
     (sb-bsd-sockets:get-host-by-name host))))

(defun fnn-anchor-udp-exchange (host port request timeout)
  "Send exactly one connected UDP datagram; return response octets or :TIMEOUT."
  (unless (and (fnn-anchor-valid-endpoint-p host port timeout)
               (typep request 'fnn-octets)
               (= (length request) +fnn-anchor-request-octets+))
    (fnn-fault "invalid bounded anchor UDP request"))
  (let ((socket (make-instance 'sb-bsd-sockets:inet-socket
                               :type :datagram :protocol :udp)))
    (unwind-protect
         (progn
           (sb-bsd-sockets:socket-connect socket (fnn-anchor-resolve-v4 host) port)
           (let ((fd (fnn-socket-fd socket)))
             (unless (sb-sys:wait-until-fd-usable fd :output timeout)
               (return-from fnn-anchor-udp-exchange :timeout))
             (unless (= (sb-bsd-sockets:socket-send socket request nil)
                        (length request))
               (fnn-fault "short anchor UDP datagram send"))
             (unless (sb-sys:wait-until-fd-usable fd :input timeout)
               (return-from fnn-anchor-udp-exchange :timeout))
             (let ((buffer (fnn-make-octets
                            +fnn-anchor-max-response-octets+)))
               (multiple-value-bind (received count peer)
                   (sb-bsd-sockets:socket-receive
                    socket buffer +fnn-anchor-max-response-octets+)
                 (declare (ignore peer))
                 (when (> count +fnn-anchor-max-response-octets+)
                   (return-from fnn-anchor-udp-exchange :overbound))
                 (subseq received 0 count)))))
      (fnn-socket-shut socket))))

(defun fnn-anchor-parse (packet nonce pinned-key)
  "Call the ACL2 parser; :REFUSED is a grammar/binding verdict, not I/O."
  (let ((result (fnn-core 'fn-anchor-wire-host-parse
                          (fnn-octet-list packet)
                          (fnn-octet-list nonce)
                          (fnn-octet-list pinned-key))))
    (unless (and (listp result) (consp result)
                 (member (first result) '(:parsed :refused)))
      (fnn-fault "ACL2 returned an invalid anchor parse result"))
    result))

(defun fnn-anchor-observe (parsed nonce)
  "Run only the Ed25519/SHA-512 observations over ACL2's parsed projection."
  (unless (and (listp parsed) (= (length parsed) 7)
               (eq (first parsed) :parsed))
    (fnn-fault "invalid ACL2 anchor projection"))
  (let* ((fields (second parsed))
         (delegation-subject (fifth parsed))
         (response-subject (sixth parsed))
         (single-leaf-shape (seventh parsed)))
    (unless (and (listp fields) (= (length fields) 10)
                 (member single-leaf-shape '(0 1)))
      (fnn-fault "invalid ACL2 anchor fields"))
    (let ((delegation
            (fnn-crypto-ed25519-observe
             (first fields) delegation-subject (fifth fields)))
          (response
            (fnn-crypto-ed25519-observe
             (second fields) response-subject (ninth fields))))
      (when (or (eq delegation :unavailable) (eq response :unavailable))
        (return-from fnn-anchor-observe '(:uncertain :crypto-unavailable)))
      (when (or (eq delegation :fault) (eq response :fault))
        (return-from fnn-anchor-observe '(:fault :crypto)))
      (handler-case
          (let ((one-nonce
                  (and (= single-leaf-shape 1)
                       (equalp (fnn-crypto-anchor-leaf nonce)
                               (fnn-crypto-octets (tenth fields) 64
                                                  "anchor root")))))
            (list :observed fields
                  (and (eq delegation :verified) (eq response :verified))
                  one-nonce))
        (fnn-crypto-unavailable () '(:uncertain :crypto-unavailable))
        (fnn-crypto-fault () '(:fault :crypto))
        (error () '(:fault :crypto))))))

(defun fnn-anchor-acquire (host port pinned-key timeout)
  "One bounded acquisition through ACL2 request/parser and native primitives."
  (handler-case
      (progn
        (unless (fnn-anchor-valid-endpoint-p host port timeout)
          (return-from fnn-anchor-acquire '(:fault :endpoint)))
        (let ((key (fnn-crypto-octets pinned-key 32 "pinned anchor key")))
          (when (/= (length key) 32)
            (return-from fnn-anchor-acquire '(:fault :pinned-key)))
          (let* ((nonce (fnn-anchor-csprng-nonce))
                 (request (fnn-anchor-request nonce))
                 (packet
                   (handler-case
                       (fnn-anchor-udp-exchange host port request timeout)
                     (sb-bsd-sockets:name-service-error () :network)
                     (sb-bsd-sockets:socket-error () :network)
                     (fnn-os-error () :network))))
            (cond ((eq packet :timeout) '(:uncertain :timeout))
                  ((eq packet :network) '(:uncertain :network))
                  ((eq packet :overbound) '(:refused :response-too-large))
                  (t
                   (let ((parsed (fnn-anchor-parse packet nonce key)))
                     (if (eq (first parsed) :refused)
                         parsed
                       (fnn-anchor-observe parsed nonce))))))))
    (fnn-crypto-unavailable () '(:uncertain :crypto-unavailable))
    (fnn-crypto-fault () '(:fault :crypto))
    (fnn-store-indeterminate () '(:uncertain :core))
    (fnn-store-fault () '(:fault :host))
    (fnn-store-error () '(:fault :core))
    (error () '(:fault :host))))
