; fn: the pinned external-anchor server manifest.
;
; The operator configuration selects a bounded name.  This book, rather than
; raw Lisp or a JSON helper, maps that name to the endpoint and long-term key
; the node trusts.  Changing this table changes trust and therefore requires
; an explicit source change and a newly certified native image.

(in-package "ACL2")
(include-book "anchor")
(include-book "anchor-wire")

(defconst *fn-anchor-server-max-timeout-seconds* 60)

(defconst *fn-anchor-server-int08h-name* '(105 110 116 48 56 104))
(defconst *fn-anchor-server-int08h-host*
  '(114 111 117 103 104 116 105 109 101 46 105 110 116 48 56 104 46 99 111 109))
(defconst *fn-anchor-server-int08h-port* 2002)
(defconst *fn-anchor-server-int08h-key*
  '(1 110 110 2 132 210 76 55 198 228 215 216 213 180 225 211
    193 148 156 234 165 69 191 135 86 22 201 220 224 201 190 193))

(defconst *fn-anchor-server-cloudflare-name*
  '(99 108 111 117 100 102 108 97 114 101))
(defconst *fn-anchor-server-cloudflare-host*
  '(114 111 117 103 104 116 105 109 101 46 99 108 111 117 100 102 108 97
    114 101 46 99 111 109))
(defconst *fn-anchor-server-cloudflare-port* 2002)
(defconst *fn-anchor-server-cloudflare-key*
  '(128 62 183 133 40 247 73 196 190 194 227 158 26 187 155 94
    90 183 228 221 92 228 182 242 253 47 147 236 195 83 143 26))

(defconst *fn-anchor-server-pinned-keys*
  (list *fn-anchor-server-int08h-key*
        *fn-anchor-server-cloudflare-key*))

; A selected record is (:server HOST-OCTETS PORT KEY PINNED-KEYS).  The last
; field is the whole node trust set passed to fn-anchor-host-accept; KEY is the
; selected server's key used to parse and verify this response.
(defun fn-anchor-server-find (name)
  (declare (xargs :guard t))
  (cond ((equal name *fn-anchor-server-int08h-name*)
         (list :server *fn-anchor-server-int08h-host*
               *fn-anchor-server-int08h-port*
               *fn-anchor-server-int08h-key*
               *fn-anchor-server-pinned-keys*))
        ((equal name *fn-anchor-server-cloudflare-name*)
         (list :server *fn-anchor-server-cloudflare-host*
               *fn-anchor-server-cloudflare-port*
               *fn-anchor-server-cloudflare-key*
               *fn-anchor-server-pinned-keys*))
        (t (list :refused :unknown-anchor-server))))

(defun fn-anchor-server-namep (name)
  (declare (xargs :guard t))
  (equal (car (fn-anchor-server-find name)) :server))

; The complete bounded acquisition profile.  Raw Lisp consumes these values;
; it does not carry a second set of wire-size or timeout policy constants.
; TIMEOUT is an operator observation in seconds, admitted only inside this
; ACL2-owned profile.
(defun fn-anchor-server-select (name timeout)
  (declare (xargs :guard t))
  (let ((server (fn-anchor-server-find name)))
    (cond ((not (equal (car server) :server)) server)
          ((not (and (natp timeout)
                     (< 0 timeout)
                     (<= timeout *fn-anchor-server-max-timeout-seconds*)))
           (list :refused :anchor-timeout))
          (t
           (list :server
                 (nth 1 server) (nth 2 server) (nth 3 server) (nth 4 server)
                 *fn-anchor-nonce-octets*
                 *fn-anchor-wire-request-octets*
                 *fn-anchor-wire-max-response*
                 timeout)))))

(defthm fn-anchor-server-find-known-shape
  (implies (fn-anchor-server-namep name)
           (and (equal (len (fn-anchor-server-find name)) 5)
                (equal (car (fn-anchor-server-find name)) :server)))
  :rule-classes nil)

(defthm fn-anchor-server-find-selected-key-is-pinned
  (implies (fn-anchor-server-namep name)
           (member-equal (nth 3 (fn-anchor-server-find name))
                         (nth 4 (fn-anchor-server-find name))))
  :rule-classes nil)

(defthm fn-anchor-server-find-selected-key-width
  (implies (fn-anchor-server-namep name)
           (fn-anchor-octets-of-lengthp
            (nth 3 (fn-anchor-server-find name)) *fn-anchor-key-octets*))
  :rule-classes nil)

(defthm fn-anchor-server-select-known-shape
  (implies (equal (car (fn-anchor-server-select name timeout)) :server)
           (and (equal (len (fn-anchor-server-select name timeout)) 9)
                (equal (nth 5 (fn-anchor-server-select name timeout))
                       *fn-anchor-nonce-octets*)
                (equal (nth 6 (fn-anchor-server-select name timeout))
                       *fn-anchor-wire-request-octets*)
                (equal (nth 7 (fn-anchor-server-select name timeout))
                       *fn-anchor-wire-max-response*)))
  :rule-classes nil)

(in-theory (disable (:d fn-anchor-server-find)
                    (:d fn-anchor-server-namep)
                    (:d fn-anchor-server-select)))
