(in-package #:3b-dex)

(defparameter *opcodes* (make-array 256 :initial-element nil))
(defparameter *opcode-names* (make-hash-table))

(defparameter *instruction-formats* (make-hash-table))

(defparameter *write-endian* :le)

#++
(defun write-u16 (x stream)
  (if (eq *write-endian* :le)
      (progn (write-byte (ldb (byte 0 0) x) stream)
             (write-byte (ldb (byte 8 0) x) stream))
      (progn (write-byte (ldb (byte 8 0) x) stream)
             (write-byte (ldb (byte 0 0) x) stream))))

(defmacro deformat (format arglist &key read write)
  ;; assuming a u-b-16 stream for now, since we are probably
  ;; reading from code already loaded into memory by .dex decoder
  ;; todo: load directly from an array
  `(setf (gethash ',format *instruction-formats*)
         (list :read (lambda (name op stream)
                       (declare (ignorable name op))
                       (flet ((next () (read-byte stream)))
                         (declare (ignorable #'next))
                         ,read))
               :write (lambda (name op stream &rest args)
                        (declare (ignorable name op))
                        (destructuring-bind ,arglist args
                          (flet ((out (x) (write-byte x stream)))
                            ,write))))))
;; :read is a form that returns a list of the form (:op-name args ...)
;;   given the NAME of the opcode being read, the first word of the
;;   instruction in OP, and a function NEXT to call to read more
;;   instruction words
;; :write is a form that should call the function OUT with any
;;   instruction words for the opcode NAME (available in numeric form
;;   as OP) with arguments specified by arglist passed to deformat

(deformat 10x ()
  :read `(,name)
  :write (out op))

(deformat 10x* ()
  :read (labels ((int ()
                   (let ((u (logior (next) (ash (next) 16))))
                     (if (logbitp 31 u)
                         (dpb u (byte 32 0) -1)
                         u)))
                 (ints (count)
                   (coerce
                    (loop for i below count collect (int))
                    'vector))
                 (elements (size count)
                   (let ((part (next))
                         (offset 0))
                     (flet ((octet ()
                              (prog2
                                  (when (= 2 offset)
                                    (setf part (next) offset 0))
                                  (ldb (byte 8 (* offset 8)) part)
                                (incf offset))))
                       (coerce (loop repeat count
                                     collect (loop for i below size
                                                   sum (ash (octet) (* i 8))))
                               'vector)))))
          (case (ldb (byte 8 8) op)
            ;; 0 = actual NOP
            (0 `(,name))
            (1 (let ((size (next)))
                 (list :packed-switch-payload
                       :first-key (int)
                       :targets (ints size))))
            (2 (let ((size (next)))
                 (list :sparse-switch-payload
                       :keys (ints size)
                       :targets (ints size))))
            (3 (let ((element-width (next))
                     (count (int)))
                 (list :fill-array-data-payload
                       ;; not sure if we need to store this, or should just
                       ;; find max size of elements?
                       ;; (need to deal with floats etc too, possibly
                       ;;  should just leave it as raw data?)
                       :element-width element-width
                       :data (elements element-width count))))))
  :write (out op))

(defmacro word (&rest fields-and-sizes)
  (let ((fields-and-sizes (copy-list fields-and-sizes)))
    `(let ,(loop for entry on fields-and-sizes by #'cddr
                 for var = (car entry)
                 for gensym = (gensym (format nil "~a" var))
                 collect (list gensym var)
                 do (setf (car entry) gensym))
       ,@(loop for (var size) on fields-and-sizes by #'cddr
               collect `(assert (<= (integer-length ,var) ,size)
                                ()
                                "failed to encode value ~d into ~d bit field?"
                                ,var ,size))
       (logior ,@(loop for (var size) on fields-and-sizes by #'cddr
                       for shift = (- 16 size) then (- shift size)
                       collect `(ash (ldb (byte ,size 0) ,var) ,shift))))))


(deformat 12x (a b)
  :read (list name (ldb (byte 4 8) op) (ldb (byte 4 12) op))
  :write (out (word b 4 a 4 op 8)))

(deformat 11n (a b)
  :read (list name (ldb (byte 4 8) op) (ldb (byte 4 12) op))
  :write (out (word b 4 a 4 op 8)))


(deformat 11x (a)
  :read (list name (ldb (byte 8 8) op))
  :write (out (word a 8 op 8)))

(deformat 10t (a)
  :read (list name (ldb (byte 8 8) op))
  :write (out (word a 8 op 8)))

(deformat 20t (a)
  :read (list name (next))
  :write (progn (out (word 0 8 op 8)) (out (word a 16))))

(deformat 20bc (a b)
  :read (list name (ldb (byte 8 8) op) (next))
  :write (progn (out (word a 8 op 8)) (out (word b 16))))

(deformat 22x (a b)
  :read (list name (ldb (byte 8 8) op) (next))
  :write (progn (out (word a 8 op 8)) (out (word b 16))))

(deformat 21t (a b)
  :read (list name (ldb (byte 8 8) op) (next))
  :write (progn (out (word a 8 op 8)) (out (word b 16))))

(deformat 21s (a b)
  :read (list name (ldb (byte 8 8) op) (next))
  :write (progn (out (word a 8 op 8)) (out (word b 16))))

;; docs don't distinguish between 32 and 64 bit versions, so split 21h
(deformat 21h32 (a b)
  :read (list name (ldb (byte 8 8) op) (ash (next) 16))
  :write (progn (out (word a 8 op 8)) (out (word (ash b -16) 16))))

(deformat 21h64 (a b)
  :read (list name (ldb (byte 8 8) op) (ash (next) 48))
  :write (progn (out (word a 8 op 8)) (out (word (ash b -48) 16))))

;; probably need to split this into type/field/string specific versions?
(deformat 21c (a b)
  :read (list name (ldb (byte 8 8) op) (next))
  :write (progn (out (word a 8 op 8)) (out (word b 16))))

(deformat 23x (a b c)
  :read (let ((n (next)))
          (list name (ldb (byte 8 8) op) (ldb (byte 8 0) n)
                (ldb (byte 8 8) n)))
  :write (progn (out (word a 8 op 8))
                (out (word c 8 b 8))))

(deformat 22b (a b c)
  :read (let ((n (next)))
          (list name (ldb (byte 8 8) op) (ldb (byte 8 0) n)
                (ldb (byte 8 8) n)))
  :write (progn (out (word a 8 op 8))
                (out (word c 8 b 8))))

(deformat 22t (a b c)
  :read (list name (ldb (byte 4 8) op) (ldb (byte 4 12) op) (next))
  :write (progn (out (word b 4 a 4 op 8))
                (out (word c 16))))

(deformat 22s (a b c)
  :read (list name (ldb (byte 4 8) op) (ldb (byte 4 12) op) (next))
  :write (progn (out (word b 4 a 4 op 8))
                (out (word c 16))))

(deformat 22c (a b c) ;; type/field variants?
  :read (list name (ldb (byte 4 8) op) (ldb (byte 4 12) op) (next))
  :write (progn (out (word b 4 a 4 op 8))
                (out (word c 16))))

(deformat 22cs (a b c)
  :read (list name (ldb (byte 4 8) op) (ldb (byte 4 12) op) (next))
  :write (progn (out (word b 4 a 4 op 8))
                (out (word c 16))))

(deformat 30t (a)
  :read (list name (logior (next) (ash (next) 16)))
  :write (progn (out (word 0 8 op 8))
                (out (ldb (byte 16 0) a))
                (out (ldb (byte 16 16) a))))

(deformat 32x (a b)
  :read (list name (next) (next))
  :write (progn (out (word 0 8 op 8))
                (out (word a 16))
                (out (word b 16))))

(deformat 31i (a b)
  :read (list name (ldb (byte 8 8) op) (logior (next) (ash (next) 16)))
  :write (progn (out (word a 8 op 8))
                (out (ldb (byte 16 0) b))
                (out (ldb (byte 16 16) b))))

(deformat 31t (a b)
  :read (list name (ldb (byte 8 8) op) (logior (next) (ash (next) 16)))
  :write (progn (out (word a 8 op 8))
                (out (ldb (byte 16 0) b))
                (out (ldb (byte 16 16) b))))

(deformat 31c (a b)
  :read (list name (ldb (byte 8 8) op) (logior (next) (ash (next) 16)))
  :write (progn (out (word a 8 op 8))
                (out (ldb (byte 16 0) b))
                (out (ldb (byte 16 16) b))))


(deformat 35c (b &rest rest) ;; A is implicit in length of REST
  :read (let* ((a (ldb (byte 4 12) op))
               (g (ldb (byte 4 8) op))
               (b (next))
               (rest (next))
               (c (ldb (byte 4 0) rest))
               (d (ldb (byte 4 4) rest))
               (e (ldb (byte 4 8) rest))
               (f (ldb (byte 4 12) rest)))
          (list* name b (subseq (list c d e f g) 0 a)))
  :write (progn (out (word (length rest) 4 (or (fifth rest) 0) 4 op 8))
                (out (word b 16))
                (out (word (or (first rest) 0) 4
                           (or (second rest) 0) 4
                           (or (third rest) 0) 4
                           (or (fourth rest) 0) 4))))

;; fixme: combine some of these formats that have the same encoders/decoders?
(deformat 35ms (b &rest rest) ;; A is implicit in length of REST
  :read (let* ((a (ldb (byte 4 12) op))
               (g (ldb (byte 4 8) op))
               (b (next))
               (rest (next))
               (c (ldb (byte 4 0) rest))
               (d (ldb (byte 4 4) rest))
               (e (ldb (byte 4 8) rest))
               (f (ldb (byte 4 12) rest)))
          (list* name b (subseq (list c d e f g) 0 a)))
  :write (progn (out (word (length rest) 4 (or (fifth rest) 0) 4 op 8))
                (out (word b 16))
                (out (word (or (first rest) 0) 4
                           (or (second rest) 0) 4
                           (or (third rest) 0) 4
                           (or (fourth rest) 0) 4))))

(deformat 35mi (b &rest rest) ;; A is implicit in length of REST
  :read (let* ((a (ldb (byte 4 12) op))
               (g (ldb (byte 4 8) op))
               (b (next))
               (rest (next))
               (c (ldb (byte 4 0) rest))
               (d (ldb (byte 4 4) rest))
               (e (ldb (byte 4 8) rest))
               (f (ldb (byte 4 12) rest)))
          (list* name b (subseq (list c d e f g) 0 a)))
  :write (progn (out (word (length rest) 4 (or (fifth rest) 0) 4 op 8))
                (out (word b 16))
                (out (word (or (first rest) 0) 4
                           (or (second rest) 0) 4
                           (or (third rest) 0) 4
                           (or (fourth rest) 0) 4))))

(deformat 3rc (a b c)
  :read (list name (ldb (byte 8 8) op) (next) (next))
  :write (progn (out (word a 8 op 8))
                (out (word b 16))
                (out (word c 16))))

(deformat 3rms (a b c)
  :read (list name (ldb (byte 8 8) op) (next) (next))
  :write (progn (out (word a 8 op 8))
                (out (word b 16))
                (out (word c 16))))

(deformat 3rmi (a b c)
  :read (list name (ldb (byte 8 8) op) (next) (next))
  :write (progn (out (word a 8 op 8))
                (out (word b 16))
                (out (word c 16))))


(deformat 51l (a b)
  :read (list name (ldb (byte 8 8) op)
              (logior (next) (ash (next) 16)
                      (ash (next) 32) (ash (next) 48)))
  :write (progn (out (word a 8 op 8))
                (out (ldb (byte 16 0) b))
                (out (ldb (byte 16 16) b))
                (out (ldb (byte 16 32) b))
                (out (ldb (byte 16 48) b))))

(integer-length 16)
(defmacro defop (opcode name args format)
  ;; ARGS is mostly for documentation atm, would be nice to use it for
  ;; slime autodoc though...
  `(progn
     (when (and (not (eq ,name :unused))
                (or (aref *opcodes* ,opcode)
                    (gethash ,name *opcode-names*)))
       (warn "redefining opcode ~2,'0x (~s) from ~2,'0x, ~s~%"
             ,opcode ',name
             (gethash ',name *opcode-names*)
             (aref *opcodes* ,opcode)))
     (setf (aref *opcodes* ,opcode)
           (list :code ,opcode :name ',name :format ',format :args ',args))
     (setf (gethash ',name *opcode-names*) ,opcode)))

;; there are some embedded data things that start with NOP, so can't
;; use 10x format directly
(defop #x00 :nop () 10x*)

(defop #x01 :move (dest src) 12x)
(defop #x02 :move/from16 (dest src) 22x)
(defop #x03 :move/16 (dest src) 32x)

(defop #x04 :move-wide (dest2 src2) 12x)
(defop #x05 :move-wide/from16 (dest2 src2) 22x)
(defop #x06 :move-wide/16 (dest2 src2) 32x)

(defop #x07 :move-object (dest src) 12x)
(defop #x08 :move-object/from16 (dest src) 22x)
(defop #x09 :move-object/16 (dest src) 32x)

(defop #x0a :move-result (dest) 11x)
(defop #x0b :move-result-wide (dest2) 11x)
(defop #x0c :move-result-object (dest) 11x)

(defop #x0d :move-exception (dest) 11x)

(defop #x0e :return-void () 10x)
(defop #x0f :return (ret) 11x)
(defop #x10 :return-wide (ret) 11x)
(defop #x11 :return-object (ret) 11x)

(defop #x12 :const/4 (dest value) 11n)
(defop #x13 :const/16 (dest value) 21s)
(defop #x14 :const (dest value) 31i)
(defop #x15 :const/high16 (dest value) 21h32)

(defop #x16 :const-wide/16 (dest value) 21s)
(defop #x17 :const-wide/32 (dest value) 31i)
(defop #x18 :const-wide (dest value) 51l)
(defop #x19 :const-wide/high16 (dest value) 21h64)

(defop #x1a :const-string (dest string) 21c)
(defop #x1b :const-string/jumbo (dest string) 31c)

(defop #x1c :const-class (dest type) 21c)

(defop #x1d :monitor-enter (ref) 11x)
(defop #x1e :monitor-exit (ref) 11x)

(defop #x1f :check-cast (ref type) 21c)
(defop #x20 :instance-of (dest ref type) 22c)

(defop #x21 :array-length (dest array-ref) 12x)

(defop #x22 :new-instance (dest type) 21c)
(defop #x23 :new-array (dest size type) 22c)

;; may need special handling for these?
(defop #x24 :filled-new-array (type &rest) 35c)
(defop #x25 :filled-new-array/range (type &rest) 3rc)

(defop #x26 :fill-array (array-ref &rest?) 31t)

(defop #x27 :throw (exception) 11x)

(defop #x28 :goto (branch) 10t)
(defop #x29 :goto/16 (branch) 20t)
(defop #x2a :goto/32 (branch) 30t)

(defop #x2b :packed-switch (test-reg &rest?) 31t)
(defop #x2c :sparse-switch (test-reg &rest?) 31t)

(defop #x2d :cmpl-float (dest first second) 23x)
(defop #x2e :cmpg-float (dest first second) 23x)
(defop #x2f :cmpl-double (dest first second) 23x)
(defop #x30 :cmpg-double (dest first second) 23x)
(defop #x31 :cmp-long (dest first second) 23x)


(defop #x32 :if-eq (first second branch) 22t)
(defop #x33 :if-ne (first second branch) 22t)
(defop #x34 :if-lt (first second branch) 22t)
(defop #x35 :if-ge (first second branch) 22t)
(defop #x36 :if-gt (first second branch) 22t)
(defop #x37 :if-le (first second branch) 22t)

(defop #x38 :if-eqz (reg branch) 22t)
(defop #x39 :if-nez (reg branch) 22t)
(defop #x3a :if-ltz (reg branch) 22t)
(defop #x3b :if-gez (reg branch) 22t)
(defop #x3c :if-gtz (reg branch) 22t)
(defop #x3d :if-lez (reg branch) 22t)


(defop #x3e :unused () 10x)
(defop #x3f :unused () 10x)
(defop #x40 :unused () 10x)
(defop #x41 :unused () 10x)
(defop #x42 :unused () 10x)
(defop #x43 :unused () 10x)

(defop #x44 :aget         (dest array index) 23x)
(defop #x45 :aget-wide    (dest array index) 23x)
(defop #x46 :aget-object  (dest array index) 23x)
(defop #x47 :aget-boolean (dest array index) 23x)
(defop #x48 :aget-byte    (dest array index) 23x)
(defop #x49 :aget-char    (dest array index) 23x)
(defop #x4a :aget-short   (dest array index) 23x)

(defop #x4b :aput         (src array index) 23x)
(defop #x4c :aput-wide    (src array index) 22x)
(defop #x4d :aput-object  (src array index) 23x)
(defop #x4e :aput-boolean (src array index) 23x)
(defop #x4f :aput-byte    (src array index) 23x)
(defop #x50 :aput-char    (src array index) 23x)
(defop #x51 :aput-short   (src array index) 23x)

(defop #x52 :iget         (dest object field) 22c)
(defop #x53 :iget-wide    (dest object field) 22c)
(defop #x54 :iget-object  (dest object field) 22c)
(defop #x55 :iget-boolean (dest object field) 22c)
(defop #x56 :iget-byte    (dest object field) 22c)
(defop #x57 :iget-char    (dest object field) 22c)
(defop #x58 :iget-short   (dest object field) 22c)

(defop #x59 :iput         (src object field) 22c)
(defop #x5a :iput-wide    (src object field) 22c)
(defop #x5b :iput-object  (src object field) 22c)
(defop #x5c :iput-boolean (src object field) 22c)
(defop #x5d :iput-byte    (src object field) 22c)
(defop #x5e :iput-char    (src object field) 22c)
(defop #x5f :iput-short   (src object field) 22c)


(defop #x60 :sget         (dest field) 21c)
(defop #x61 :sget-wide    (dest field) 21c)
(defop #x62 :sget-object  (dest field) 21c)
(defop #x63 :sget-boolean (dest field) 21c)
(defop #x64 :sget-byte    (dest field) 21c)
(defop #x65 :sget-char    (dest field) 21c)
(defop #x66 :sget-short   (dest field) 21c)

(defop #x67 :sput         (src field) 21c)
(defop #x68 :sput-wide    (src field) 21c)
(defop #x69 :sput-object  (src field) 21c)
(defop #x6a :sput-boolean (src field) 21c)
(defop #x6b :sput-byte    (src field) 21c)
(defop #x6c :sput-char    (src field) 21c)
(defop #x6d :sput-short   (src field) 21c)

(defop #x6e :invoke-virtual (method &rest) 35c)
(defop #x6f :invoke-super (method &rest) 35c)
(defop #x70 :invoke-direct (method &rest) 35c)
(defop #x71 :invoke-static (method &rest) 35c)
(defop #x72 :invoke-interface (method &rest) 35c)

(defop #x73 :unused () 10xe)

(defop #x74 :invoke-virtual/range (count method first-reg) 3rc)
(defop #x75 :invoke-super/range (count method first-reg) 3rc)
(defop #x76 :invoke-direct/range (count method first-reg) 3rc)
(defop #x77 :invoke-static/range (count method first-reg) 3rc)
(defop #x78 :invoke-interface/range (count method first-reg) 3rc)

(defop #x79 :unused () 10xe)
(defop #x7a :unused () 10xe)

(defop #x7b :neg-int (dest source) 12x)
(defop #x7c :not-int (dest source) 12x)
(defop #x7d :neg-long (dest source) 12x)
(defop #x7e :not-long (dest source) 12x)
(defop #x7f :neg-float (dest source) 12x)
(defop #x80 :neg-double (dest source) 12x)
(defop #x81 :int-to-long (dest source) 12x)
(defop #x82 :int-to-float (dest source) 12x)
(defop #x83 :int-to-double (dest source) 12x)
(defop #x84 :long-to-int (dest source) 12x)
(defop #x85 :long-to-float (dest source) 12x)
(defop #x86 :long-to-double (dest source) 12x)
(defop #x87 :float-to-int (dest source) 12x)
(defop #x88 :float-to-long (dest source) 12x)
(defop #x89 :float-to-double (dest source) 12x)
(defop #x8a :double-to-int (dest source) 12x)
(defop #x8b :double-to-long (dest source) 12x)
(defop #x8c :double-to-float (dest source) 12x)
(defop #x8d :int-to-byte (dest source) 12x)
(defop #x8e :int-to-char (dest source) 12x)
(defop #x8f :int-to-short (dest source) 12x)

(defop #x90 :add-int (dest source1 source2) 23x)
(defop #x91 :sub-int (dest source1 source2) 23x)
(defop #x92 :mul-int (dest source1 source2) 23x)
(defop #x93 :div-int (dest source1 source2) 23x)
(defop #x94 :rem-int (dest source1 source2) 23x)
(defop #x95 :and-int (dest source1 source2) 23x)
(defop #x96 :or-int (dest source1 source2) 23x)
(defop #x97 :xor-int (dest source1 source2) 23x)
(defop #x98 :shl-int (dest source1 source2) 23x)
(defop #x99 :shr-int (dest source1 source2) 23x)
(defop #x9a :ushr-int (dest source1 source2) 23x)
(defop #x9b :add-long (dest source1 source2) 23x)
(defop #x9c :sub-long (dest source1 source2) 23x)
(defop #x9d :mul-long (dest source1 source2) 23x)
(defop #x9e :div-long (dest source1 source2) 23x)
(defop #x9f :rem-long (dest source1 source2) 23x)
(defop #xa0 :and-long (dest source1 source2) 23x)
(defop #xa1 :or-long (dest source1 source2) 23x)
(defop #xa2 :xor-long (dest source1 source2) 23x)
(defop #xa3 :shl-long (dest source1 source2) 23x)
(defop #xa4 :shr-long (dest source1 source2) 23x)
(defop #xa5 :ushr-long (dest source1 source2) 23x)
(defop #xa6 :add-float (dest source1 source2) 23x)
(defop #xa7 :sub-float (dest source1 source2) 23x)
(defop #xa8 :mul-float (dest source1 source2) 23x)
(defop #xa9 :div-float (dest source1 source2) 23x)
(defop #xaa :rem-float (dest source1 source2) 23x)
(defop #xab :add-double (dest source1 source2) 23x)
(defop #xac :sub-double (dest source1 source2) 23x)
(defop #xad :mul-double (dest source1 source2) 23x)
(defop #xae :div-double (dest source1 source2) 23x)
(defop #xaf :rem-double (dest source1 source2) 23x)


(defop #xb0 :add-int/2addr (dest/src1 source2) 12x)
(defop #xb1 :sub-int/2addr (dest/src1 source2) 12x)
(defop #xb2 :mul-int/2addr (dest/src1 source2) 12x)
(defop #xb3 :div-int/2addr (dest/src1 source2) 12x)
(defop #xb4 :rem-int/2addr (dest/src1 source2) 12x)
(defop #xb5 :and-int/2addr (dest/src1 source2) 12x)
(defop #xb6 :or-int/2addr (dest/src1 source2) 12x)
(defop #xb7 :xor-int/2addr (dest/src1 source2) 12x)
(defop #xb8 :shl-int/2addr (dest/src1 source2) 12x)
(defop #xb9 :shr-int/2addr (dest/src1 source2) 12x)
(defop #xba :ushr-int/2addr (dest/src1 source2) 12x)
(defop #xbb :add-long/2addr (dest/src1 source2) 12x)
(defop #xbc :sub-long/2addr (dest/src1 source2) 12x)
(defop #xbd :mul-long/2addr (dest/src1 source2) 12x)
(defop #xbe :div-long/2addr (dest/src1 source2) 12x)
(defop #xbf :rem-long/2addr (dest/src1 source2) 12x)
(defop #xc0 :and-long/2addr (dest/src1 source2) 12x)
(defop #xc1 :or-long/2addr (dest/src1 source2) 12x)
(defop #xc2 :xor-long/2addr (dest/src1 source2) 12x)
(defop #xc3 :shl-long/2addr (dest/src1 source2) 12x)
(defop #xc4 :shr-long/2addr (dest/src1 source2) 12x)
(defop #xc5 :ushr-long/2addr (dest/src1 source2) 12x)
(defop #xc6 :add-float/2addr (dest/src1 source2) 12x)
(defop #xc7 :sub-float/2addr (dest/src1 source2) 12x)
(defop #xc8 :mul-float/2addr (dest/src1 source2) 12x)
(defop #xc9 :div-float/2addr (dest/src1 source2) 12x)
(defop #xca :rem-float/2addr (dest/src1 source2) 12x)
(defop #xcb :add-double/2addr (dest/src1 source2) 12x)
(defop #xcc :sub-double/2addr (dest/src1 source2) 12x)
(defop #xcd :mul-double/2addr (dest/src1 source2) 12x)
(defop #xce :div-double/2addr (dest/src1 source2) 12x)
(defop #xcf :rem-double/2addr (dest/src1 source2) 12x)

(defop #xd0 :add-int/lit16 (dest source const) 22s)
(defop #xd1 :rsub-int/lit16 (dest source const) 22s)
(defop #xd2 :mul-int/lit16 (dest source const) 22s)
(defop #xd3 :div-int/lit16 (dest source const) 22s)
(defop #xd4 :rem-int/lit16 (dest source const) 22s)
(defop #xd5 :and-int/lit16 (dest source const) 22s)
(defop #xd6 :or-int/lit16 (dest source const) 22s)
(defop #xd7 :xor-int/lit16 (dest source const) 22s)

(defop #xd8 :add-int/lit8 (dest source const) 22b)
(defop #xd9 :rsub-int/lit8 (dest source const) 22b)
(defop #xda :mul-int/lit8 (dest source const) 22b)
(defop #xdb :div-int/lit8 (dest source const) 22b)
(defop #xdc :rem-int/lit8 (dest source const) 22b)
(defop #xdd :and-int/lit8 (dest source const) 22b)
(defop #xde :or-int/lit8 (dest source const) 22b)
(defop #xdf :xor-int/lit8 (dest source const) 22b)
(defop #xe0 :shr-int/lit8 (dest source const) 22b)
(defop #xe1 :shl-int/lit8 (dest source const) 22b)
(defop #xe2 :ushr-int/lit8 (dest source const) 22b)

(defop #xe3 :unused () 10xe)
(defop #xe4 :unused () 10xe)
(defop #xe5 :unused () 10xe)
(defop #xe6 :unused () 10xe)
(defop #xe7 :unused () 10xe)
(defop #xe8 :unused () 10xe)
(defop #xe9 :unused () 10xe)
(defop #xea :unused () 10xe)
(defop #xeb :unused () 10xe)
(defop #xec :unused () 10xe)
(defop #xed :unused () 10xe)
(defop #xef :unused () 10xe)
(defop #xf0 :unused () 10xe)
(defop #xf1 :unused () 10xe)
(defop #xf2 :unused () 10xe)
(defop #xf3 :unused () 10xe)
(defop #xf4 :unused () 10xe)
(defop #xf5 :unused () 10xe)
(defop #xf6 :unused () 10xe)
(defop #xf7 :unused () 10xe)
(defop #xf8 :unused () 10xe)
(defop #xf9 :unused () 10xe)
(defop #xfa :unused () 10xe)
(defop #xfb :unused () 10xe)
(defop #xfc :unused () 10xe)
(defop #xfd :unused () 10xe)
(defop #xff :unused () 10xe)



(defun unassemble (code)
  (flex:with-input-from-sequence (s code)
    (loop for instruction = (read-byte s nil)
          for op = (when instruction (ldb (byte 8 0) instruction))
          for op-name = (when op (getf (aref *opcodes* op) :name))
          for format = (when op (getf (aref *opcodes* op) :format))
          for reader = (when op
                         (getf (gethash format *instruction-formats*) :read))
          while instruction
          collect (funcall reader op-name instruction s))))


#++
(unassemble #(26 2536 4209 1403 0 14))
