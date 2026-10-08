; Teeth for books/decision-trace-config.lisp: the profile's [trace] table
; becomes a plan, or a refusal by the name of the key or rule.  A reachable
; witness for each accepted shape, and one witness per refusal with everything
; else right (the hypothesis-removal witness).

(in-package "ACL2")
(include-book "../../books/decision-trace-config")

(defmacro fn-dtc-plan (text image)
  `(fn-dtrace-config-plan (fn-record-string-octets ,(concatenate 'string "[store]
path = \"/s\"
" text)) ,image))

; no table, an empty table: nothing traced, nothing charged
(assert-event (equal (fn-dtc-plan "" :production) '(:off)))
(assert-event (equal (fn-dtc-plan "[listener]
port = 1119
" :developer) '(:off)))

; the defaults of a table with one key
(assert-event (equal (fn-dtc-plan "[trace]
capacity = 16
" :production)
                     '(:plan (:verdict :refusal :tariff :schedule :plan) 16 1 nil nil 0)))
(assert-event (equal (fn-dtrace-ring-octets (fn-dtc-plan "[trace]
capacity = 16
" :production))
                     (+ 4096 (* 1024 16))))
; every key
(assert-event (equal (fn-dtc-plan "[trace]
classes = \"schedule,verdict\"
capacity = 8
sample_every = 5
allocation = \"process\"
start = \"on\"
rss_every = 3
" :production)
                     '(:plan (:schedule :verdict) 8 5 :process t 3)))
(assert-event (equal (fn-dtc-plan "[trace]
classes = \"all\"
allocation = \"isolated-process\"
" :developer)
                     '(:plan (:verdict :refusal :tariff :schedule :plan) 1024 1
                       :isolated-process nil 0)))

; refusals, by name
(assert-event (equal (fn-dtc-plan "[trace]
classes = \"verdict,elsewhere\"
" :production) '(:refused :classes)))
(assert-event (equal (fn-dtc-plan "[trace]
classes = \"verdict,,tariff\"
" :production) '(:refused :classes)))
(assert-event (equal (fn-dtc-plan "[trace]
classes = \"verdict,verdict\"
" :production) '(:refused :duplicate-class)))
(assert-event (equal (fn-dtc-plan "[trace]
capacity = 0
" :production) '(:refused :capacity)))
(assert-event (equal (fn-dtc-plan "[trace]
capacity = 65537
" :production) '(:refused :capacity)))
(assert-event (equal (fn-dtc-plan "[trace]
sample_every = 0
" :production) '(:refused :sample-every)))
(assert-event (equal (fn-dtc-plan "[trace]
allocation = \"heap\"
" :production) '(:refused :allocation)))
(assert-event (equal (fn-dtc-plan "[trace]
allocation = \"isolated-process\"
" :production) '(:refused :isolated-allocation-needs-developer-image)))
(assert-event (equal (fn-dtc-plan "[trace]
start = \"maybe\"
" :production) '(:refused :start)))
(assert-event (equal (fn-dtc-plan "[trace]
rss_every = 1000001
" :production) '(:refused :rss-every)))
; a key the table does not have is a configuration syntax refusal
(assert-event (equal (fn-dtc-plan "[trace]
path = \"/x\"
" :production) '(:refused :syntax)))
; a value of the wrong kind
(assert-event (equal (fn-dtc-plan "[trace]
capacity = \"big\"
" :production) '(:refused :capacity)))

(assert-event (equal (fn-dtrace-plan-kind '(:off)) :off))
(assert-event (equal (fn-dtrace-plan-kind (fn-dtc-plan "[trace]
capacity = 4
" :production)) :plan))
(assert-event (equal (fn-dtrace-plan-kind '(:refused :capacity)) :refused))
(assert-event (equal (fn-dtrace-plan-refusal '(:refused :capacity)) :capacity))
(assert-event (null (fn-dtrace-plan-refusal '(:off))))
