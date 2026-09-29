; Every field of a configuration record (books/config.lisp) at its maximum
; allowed value round-trips through the record codec, and one past each
; maximum is refused by name.  Lane clock-units-2 (2026-09-28): a
; millisecond stamp past 2^32 was admitted by fn-cfg-stampp but written with
; the narrow CBOR uint, so every native `init' faulted at open; nothing
; encoded a field at its maximum.  This book is that check.
;
; THE MAXIMA, each the recognizer that states it:
;   sequence, txid, generation   fn-record-uint32p        2^32 - 1
;   stamp monotonic/wall/error   fn-clock-timep           2^64 - 1 (ms)
;   stamp has-wall               booleanp                 t (item 1)
;   delta count                  *fn-cfg-max-deltas*      64
;   delta kind                   *fn-cfg-delta-kinds*     code 28
;   delta a, b; row a, b, c      fn-cfg-labelp            256 octets
;   delta n, row n               fn-record-uint32p        2^32 - 1
;   rows per delta               *fn-cfg-max-rows*        1024
;   items per record             *fn-cfg-max-items*       65535
;   octets per record            *fn-cfg-max-octets*      65538
; The last two are the decoder's whole-record ceilings.  They are NOT part
; of fn-cfg-recordp: a record every field of which is within its maximum can
; encode past 65,538 octets, and the decoder then refuses it :limit.  So
; admission checks them: fn-cfg-record-acceptablep requires
; fn-cfg-record-fitsp, which is exactly the decoder's two limits
; (fn-cfg-record-fitsp-is-the-decoder-limits).  Below, the REFUSAL witnesses:
; at 65,538 octets the record is accepted and round-trips; at 65,539 the
; same record, admissible in every other conjunct, is refused at admission,
; as the decoder refuses its octets (lane config-and-legacy).
(in-package "ACL2")
(include-book "../../books/config")

(defconst *cfm-u32* *fn-cbor-max-uint*)
(defconst *cfm-u64* *fn-clock-max*)
(defconst *cfm-label* (coerce (make-list *fn-cfg-max-label* :initial-element #\z)
                              'string))
(defconst *cfm-label+1* (coerce (make-list (+ 1 *fn-cfg-max-label*)
                                           :initial-element #\z)
                                'string))
(defconst *cfm-stamp* (fn-clock-observation *cfm-u64* *cfm-u64* *cfm-u64* t))
(defconst *cfm-row* (fn-cfg-row-make *cfm-label* *cfm-label* *cfm-label* *cfm-u32*))
(defconst *cfm-delta*
  (fn-cfg-delta-make :reclaim-note *cfm-label* *cfm-label* *cfm-u32*
                     (list *cfm-row*)))

(defmacro cfm-round-trips (r)
  `(and (fn-cfg-recordp ,r)
        (equal (fn-cfg-decode-exact (fn-cfg-encode ,r))
               (fn-record-parse-ok ,r nil))))

; Every scalar and every label at its maximum, the last kind code.
(defconst *cfm-max*
  (fn-cfg-record-make *cfm-u32* *cfm-u32* *cfm-u32* (list *cfm-delta*) *cfm-stamp*))
(assert-event (equal (fn-cfg-kind-code :account-delete) 27))
(assert-event (equal (fn-cfg-kind-code :reclaim-note) 28))
(assert-event (cfm-round-trips *cfm-max*))

; The stamp at its maximum without a wall claim.
(assert-event
 (cfm-round-trips
  (fn-cfg-record-make 0 0 1 (list *cfm-delta*)
                      (fn-clock-observation *cfm-u64* *cfm-u64* *cfm-u64* nil))))

; The delta count at its maximum.
(defconst *cfm-64*
  (fn-cfg-record-make 1 1 2 (make-list *fn-cfg-max-deltas*
                                       :initial-element (fn-cfg-remove-group "g"))
                      *cfm-stamp*))
(assert-event (cfm-round-trips *cfm-64*))

; The rows of one delta at their maximum (short labels: at 256 octets each,
; 1,024 rows are far past the record's octet ceiling).
(defconst *cfm-1024*
  (fn-cfg-record-make 1 1 2
                      (list (fn-cfg-delta-make
                             :set-peers "" "" *cfm-u32*
                             (make-list *fn-cfg-max-rows*
                                        :initial-element
                                        (fn-cfg-row-make "a" "b" "c" *cfm-u32*))))
                      *cfm-stamp*))
(assert-event (cfm-round-trips *cfm-1024*))

; One past each maximum: never a record, and the codec refuses it by name.
(defmacro cfm-refused (r)
  `(and (not (fn-cfg-recordp ,r))
        (not (fn-record-parse-okp (fn-cfg-decode-exact (fn-cfg-encode ,r))))))
(assert-event (cfm-refused (fn-cfg-record-make (+ 1 *cfm-u32*) 0 1 (list *cfm-delta*)
                                               *cfm-stamp*)))
(assert-event (cfm-refused (fn-cfg-record-make 0 (+ 1 *cfm-u32*) 1 (list *cfm-delta*)
                                               *cfm-stamp*)))
(assert-event (cfm-refused (fn-cfg-record-make 0 0 (+ 1 *cfm-u32*) (list *cfm-delta*)
                                               *cfm-stamp*)))
(assert-event
 (cfm-refused (fn-cfg-record-make 0 0 1 (list (fn-cfg-delta-make
                                               :account-delete *cfm-label+1* "" 0 nil))
                                  *cfm-stamp*)))
(assert-event
 (cfm-refused (fn-cfg-record-make 0 0 1 (list (fn-cfg-delta-make
                                               :account-delete "" "" (+ 1 *cfm-u32*) nil))
                                  *cfm-stamp*)))
(assert-event
 (cfm-refused (fn-cfg-record-make
               0 0 1 (list (fn-cfg-delta-make
                            :set-peers "" "" 0
                            (list (fn-cfg-row-make "" "" *cfm-label+1* 0))))
               *cfm-stamp*)))
(assert-event
 (cfm-refused (fn-cfg-record-make
               0 0 1 (list (fn-cfg-delta-make
                            :set-peers "" "" 0
                            (list (fn-cfg-row-make "" "" "" (+ 1 *cfm-u32*)))))
               *cfm-stamp*)))
(assert-event
 (cfm-refused (fn-cfg-record-make 1 1 2 (make-list (+ 1 *fn-cfg-max-deltas*)
                                                   :initial-element
                                                   (fn-cfg-remove-group "g"))
                                  *cfm-stamp*)))
(assert-event
 (cfm-refused (fn-cfg-record-make
               1 1 2 (list (fn-cfg-delta-make
                            :set-peers "" "" 0
                            (make-list (+ 1 *fn-cfg-max-rows*)
                                       :initial-element (fn-cfg-row-make "a" "b" "c" 0))))
               *cfm-stamp*)))
; A stamp time past 2^64 - 1 is no clock time, so no record stamp.
(assert-event
 (not (fn-cfg-recordp (fn-cfg-record-make 0 0 1 (list *cfm-delta*)
                                          (fn-clock-observation (+ 1 *cfm-u64*) 0 0 t)))))
(assert-event (not (fn-cfg-deltap (fn-cfg-delta-make :no-such-kind "" "" 0 nil))))

;; Whole-record limits at admission (fn-cfg-record-fitsp in
;; fn-cfg-record-acceptablep).  EDGE is a :set-peers record of 84 rows whose
;; first row's third label has L octets: at L = 58 it encodes to exactly
;; *fn-cfg-max-octets* octets, at L = 59 one past.
(defconst *cfm-gen1* (fn-config-replay 0 512 (list *fn-cfg-default-record*)))
(defun cfm-edge (l)
  (fn-cfg-record-make
   1 1 2
   (list (fn-cfg-delta-make
          :set-peers "" "" 0
          (cons (fn-cfg-row-make *cfm-label* *cfm-label*
                                 (coerce (make-list l :initial-element #\y) 'string)
                                 *cfm-u32*)
                (make-list 83 :initial-element *cfm-row*))))
   *cfm-stamp*))
(assert-event (and (fn-cfgp *cfm-gen1*) (equal (fn-cfg-generation *cfm-gen1*) 1)))

; Positive witness, at the limit: every conjunct of acceptance holds, the
; encoding is exactly the octet limit, and it decodes to the record.
(assert-event
 (let ((r (cfm-edge 58)))
   (and (equal (len (fn-cfg-encode r)) *fn-cfg-max-octets*)
        (<= (len (fn-cfg-record-items r)) *fn-cfg-max-items*)
        (fn-cfg-record-fitsp r)
        (fn-cfg-recordp r)
        (equal (fn-cfg-record-generation r) (+ 1 (fn-cfg-generation *cfm-gen1*)))
        (fn-cfg-admissiblep (fn-cfg-value *cfm-gen1*) 2 (fn-cfg-record-stamp r) 0 512
                            (fn-cfg-record-change r))
        (fn-cfg-record-acceptablep *cfm-gen1* r 0 512)
        (cfm-round-trips r))))

; Removal witness, one octet past: every other conjunct of acceptance still
; holds; fitsp fails, so acceptance fails, and the decoder refuses the
; octets :limit.
(assert-event
 (let ((r (cfm-edge 59)))
   (and (equal (len (fn-cfg-encode r)) (+ 1 *fn-cfg-max-octets*))
        (fn-cfg-recordp r)
        (equal (fn-cfg-record-generation r) (+ 1 (fn-cfg-generation *cfm-gen1*)))
        (fn-cfg-admissiblep (fn-cfg-value *cfm-gen1*) 2 (fn-cfg-record-stamp r) 0 512
                            (fn-cfg-record-change r))
        (not (fn-cfg-record-fitsp r))
        (not (fn-cfg-record-acceptablep *cfm-gen1* r 0 512))
        (equal (fn-cfg-decode-exact (fn-cfg-encode r))
               (fn-record-parse-error :limit)))))

; The former GAP record (100 rows of three 256-octet labels): a record, not
; one admission accepts, and not one the codec carries.
(defconst *cfm-gap*
  (fn-cfg-record-make 1 1 2
                      (list (fn-cfg-delta-make :set-peers "" "" 0
                                               (make-list 100 :initial-element
                                                          *cfm-row*)))
                      *cfm-stamp*))
(assert-event
 (and (fn-cfg-recordp *cfm-gap*)
      (not (fn-cfg-record-fitsp *cfm-gap*))
      (not (fn-cfg-record-acceptablep *cfm-gen1* *cfm-gap* 0 512))
      (< *fn-cfg-max-octets* (len (fn-cfg-encode *cfm-gap*)))
      (equal (fn-cfg-decode-exact (fn-cfg-encode *cfm-gap*))
             (fn-record-parse-error :limit))))
