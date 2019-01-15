(in-package #:3b-dex)

;; mapping of numbers to names
(defparameter *opcode-index* (make-array 256 :initial-element nil))
;; actual opcode definitions (indexed by name rather than number so we
;; can mix in pseudo-ops and higher-level ops as well
(defparameter *opcodes* (make-hash-table))

(defparameter *instruction-formats* (make-hash-table))

(defparameter *write-endian* :le)

(defun write-u16 (x stream)
  (if (eq *write-endian* :le)
      (progn (write-byte (ldb (byte 8 0) x) stream)
             (write-byte (ldb (byte 8 8) x) stream))
      (progn (write-byte (ldb (byte 8 8) x) stream)
             (write-byte (ldb (byte 8 0) x) stream))))

(defun write-u32 (x stream)
  (if (eq *write-endian* :le)
      (progn (write-byte (ldb (byte 8 0) x) stream)
             (write-byte (ldb (byte 8 8) x) stream)
             (write-byte (ldb (byte 8 16) x) stream)
             (write-byte (ldb (byte 8 24) x) stream))
      (progn (write-byte (ldb (byte 8 24) x) stream)
             (write-byte (ldb (byte 8 16) x) stream)
             (write-byte (ldb (byte 8 8) x) stream)
             (write-byte (ldb (byte 8 0) x) stream))))

(defmacro deformat (format arglist &key read write (size (digit-char-p (char (string format) 0))))
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
                            ,write)))
               :size ,size)))
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

(defun sign-extend4 (b)
  (if (logbitp 3 b) (dpb b (byte 4 0) -1) b))
(defun sign-extend8 (b)
  (if (logbitp 7 b) (dpb b (byte 8 0) -1) b))
(defun sign-extend16 (b)
  (if (logbitp 15 b) (dpb b (byte 16 0) -1) b))
(defun sign-extend32 (b)
  (if (logbitp 31 b) (dpb b (byte 32 0) -1) b))
(defun sign-extend64 (b)
  (if (logbitp 63 b) (dpb b (byte 64 0) -1) b))

(deformat 12x (a b)
  :read (list name (ldb (byte 4 8) op) (ldb (byte 4 12) op))
  :write (out (word b 4 a 4 op 8)))

(deformat 11n (a b)
  :read (list name (ldb (byte 4 8) op) (sign-extend4 (ldb (byte 4 12) op)))
  :write (out (word b 4 a 4 op 8)))


(deformat 11x (a)
  :read (list name (ldb (byte 8 8) op))
  :write (out (word a 8 op 8)))

(deformat 10t (a)
  :read (list name (sign-extend8 (ldb (byte 8 8) op)))
  :write (out (word a 8 op 8)))

(deformat 20t (a)
  :read (list name (sign-extend16 (next)))
  :write (progn (out (word 0 8 op 8)) (out (word a 16))))

(deformat 20bc (a b)
  :read (list name (ldb (byte 8 8) op) (next))
  :write (progn (out (word a 8 op 8)) (out (word b 16))))

(deformat 22x (a b)
  :read (list name (ldb (byte 8 8) op) (next))
  :write (progn (out (word a 8 op 8)) (out (word b 16))))

(deformat 21t (a b)
  :read (list name (ldb (byte 8 8) op) (sign-extend16 (next)))
  :write (progn (out (word a 8 op 8)) (out (word b 16))))

(deformat 21s (a b)
  :read (list name (ldb (byte 8 8) op) (sign-extend16 (next)))
  :write (progn (out (word a 8 op 8)) (out (word b 16))))

;; docs don't distinguish between 32 and 64 bit versions, so split 21h
(deformat 21h32 (a b)
  :read (list name (ldb (byte 8 8) op) (sign-extend32 (ash (next) 16)))
  :write (progn (out (word a 8 op 8)) (out (word (ash b -16) 16))))

(deformat 21h64 (a b)
  :read (list name (ldb (byte 8 8) op) (sign-extend64 (ash (next) 48)))
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
  :read (list name (ldb (byte 4 8) op) (ldb (byte 4 12) op)
              (sign-extend16 (next)))
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
  :read (list name (sign-extend32 (logior (next) (ash (next) 16))))
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

(deformat 31t (a b1)
  ;; b1 can be a signed or unsigned 32 bit int, or a single float
  ;; we always decode as unsigned int for now though, since no way
  ;; to tell which it is
  :read (list name (ldb (byte 8 8) op)
              (sign-extend32 (logior (next) (ash (next) 16))))
  :write (let ((b (if (floatp b1)
                      (ieee-floats:encode-float32 b1)
                      b1)))
           (out (word a 8 op 8))
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
                (out (word (or (fourth rest) 0) 4
                           (or (third rest) 0) 4
                           (or (second rest) 0) 4
                           (or (first rest) 0) 4))))

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

(deformat 51l (a b1)
  ;; b1 can be a signed or unsigned 64 bit int, or a double float
  ;; we always decode as unsigned int for now though, since no way
  ;; to tell which it is
  :read (list name (ldb (byte 8 8) op)
              (logior (next) (ash (next) 16)
                      (ash (next) 32) (ash (next) 48)))
  :write (let ((b (etypecase b1
                    (single-float
                     (ieee-floats:encode-float32 b1))
                    (double-float
                     (ieee-floats:encode-float64 b1))
                    (integer
                     b1))))
           (out (word a 8 op 8))
           (out (ldb (byte 16 0) b))
           (out (ldb (byte 16 16) b))
           (out (ldb (byte 16 32) b))
           (out (ldb (byte 16 48) b))))

(integer-length 16)
(defmacro defop (opcode name args format types)
  ;; ARGS is mostly for documentation atm, would be nice to use it for
  ;; slime autodoc though...
  `(progn
     (when (and (not (eq ,name :unused))
                (or (aref *opcode-index* ,opcode)
                    (gethash ,name *opcodes*)))
       (warn "redefining opcode ~2,'0x (~s) from ~2,'0x, ~s~%"
             ,opcode ',name
             (gethash ',name *opcodes*)
             (aref *opcode-index* ,opcode)))
     (setf (aref *opcode-index* ,opcode)
           ',name)
     (setf (gethash ',name *opcodes*)
           (list :code ,opcode :name ',name :format ',format :args ',args
                 :types ',types
                 :size (lambda (op &rest args)
                         (declare (ignore op args))
                         (let ((s (getf (gethash ',format *instruction-formats*)
                                        :size)))
                           (values s s)))
                 :read (lambda (&rest args)
                         (apply (getf (gethash ',format
                                               *instruction-formats*)
                                      :read)
                                args))
                 :write (lambda (&rest args)
                          (apply (getf (gethash ',format
                                                *instruction-formats*)
                                       :write)
                                 args))))))

;; there are some embedded data things that start with NOP, so can't
;; use 10x format directly
(defop #x00 :nop () 10x* ())

;; arg descriptions:
;; -- not sure if these should actually distinguish sizes of the indices?
;;  :reg4 :reg8 :reg16 = 4/8/16 bit index of unspecified type single register
;;  :regn4 :regn8 :regn16 = 4/8/16 bit index of non-object register
;;  :regp4 :regp8 :regp16 = 4/8/16 bit index of register pair
;;  :rego4 :rego8 :rego16 = 4/8/16 bit index of object-bearing register
;;  :rega4 :rega8 :rega16 = 4/8/16 bit index of register containing array
;;  :lit32 = unspecified 32 bit literal
;;  :lit32s = signed 32bit constant (possibly only storing some of the bits)
;;  :string = string <-> index into string table
;;  :class, :type, :array = type designator <-> index into type table
;;  :branch offset of some other code location (including NOP tables)

;; todo: probably should mark which registers are read, written, or point to
;;       something read or written?
(defop #x01 :move (dest src) 12x (:regn4 :regn4))
(defop #x02 :move/from16 (dest src) 22x (:regn8 :regn16))
(defop #x03 :move/16 (dest src) 32x (:regn16 :regn16))

(defop #x04 :move-wide (dest2 src2) 12x (:regp4 :regp4))
(defop #x05 :move-wide/from16 (dest2 src2) 22x (:regp8 :regp16))
(defop #x06 :move-wide/16 (dest2 src2) 32x (:regp16 :regp16))

(defop #x07 :move-object (dest src) 12x (:rego4 :rego4))
(defop #x08 :move-object/from16 (dest src) 22x (:rego8 :rego16))
(defop #x09 :move-object/16 (dest src) 32x (:rego16 :rego16))

(defop #x0a :move-result (dest) 11x (:regn8))
(defop #x0b :move-result-wide (dest2) 11x (:regp8))
(defop #x0c :move-result-object (dest) 11x (:rego8))

(defop #x0d :move-exception (dest) 11x (:rego8)) ;; assuming exception is an object?

(defop #x0e :return-void () 10x ())
(defop #x0f :return (ret) 11x (:regn8))
(defop #x10 :return-wide (ret) 11x (:regp8))
(defop #x11 :return-object (ret) 11x (:rego8))

;; not sure if literals should be described by nominal size of the
;; expanded value, or by the number of bits actually stored?
(defop #x12 :const/4 (dest value) 11n (:regn4 :lit32s))
(defop #x13 :const/16 (dest value) 21s (:regn8 :lit32s))
(defop #x14 :const (dest value) 31i (:regn8 :lit32))
(defop #x15 :const/high16 (dest value) 21h32 (:regn8 :lit32))

(defop #x16 :const-wide/16 (dest value) 21s (:regp8 :lit64s))
(defop #x17 :const-wide/32 (dest value) 31i (:regp8 :lit64s))
(defop #x18 :const-wide (dest value) 51l (:regp8 :lit64))
(defop #x19 :const-wide/high16 (dest value) 21h64 (:regp8 :lit64s))

(defop #x1a :const-string (dest string) 21c (:rego8 :string))
(defop #x1b :const-string/jumbo (dest string) 31c (:rego8 :string))

(defop #x1c :const-class (dest type) 21c (:rego8 :class))

;; docs describe these as 'reference-bearing' rather than 'object-bearing'
;; not sure if that is different or not?
(defop #x1d :monitor-enter (ref) 11x (:rego8))
(defop #x1e :monitor-exit (ref) 11x (:rego8))

(defop #x1f :check-cast (ref type) 21c (:rego8 :type))
(defop #x20 :instance-of (dest ref type) 22c (:regn4 :rego4 :type))

(defop #x21 :array-length (dest array-ref) 12x (:regn4 :rego4))

(defop #x22 :new-instance (dest type) 21c (:rego8 :type)) ;; :class?
(defop #x23 :new-array (dest size type) 22c (:rego4 :regn4 :array))

;; not sure if these should indicate optional args?
(defop #x24 :filled-new-array (type &rest) 35c (:type :reg4 :reg4 :reg4 :reg4 :reg4))
(defop #x25 :filled-new-array/range (size type base) 3rc (:lit8 :type :reg16))

(defop #x26 :fill-array (array-ref branch) 31t (:array :lit-array))

(defop #x27 :throw (exception) 11x (:rego8))

(defop #x28 :goto (branch) 10t (:branch8))
(defop #x29 :goto/16 (branch) 20t (:branch16))
(defop #x2a :goto/32 (branch) 30t (:branch32))

(defop #x2b :packed-switch (test-reg targets) 31t (:regn8 :packed-switch))
(defop #x2c :sparse-switch (test-reg targets) 31t (:regn8 :sparse-switch))

(defop #x2d :cmpl-float (dest first second) 23x (:regn8 :regn8 :regn8))
(defop #x2e :cmpg-float (dest first second) 23x (:regn8 :regn8 :regn8))
(defop #x2f :cmpl-double (dest first second) 23x (:regn8 :regp8 :regp8))
(defop #x30 :cmpg-double (dest first second) 23x (:regn8 :regp8 :regp8))
(defop #x31 :cmp-long (dest first second) 23x (:regn8 :regp8 :regp8))


(defop #x32 :if-eq (first second branch) 22t (:regn4 :regn4 :branch16))
(defop #x33 :if-ne (first second branch) 22t (:regn4 :regn4 :branch16))
(defop #x34 :if-lt (first second branch) 22t (:regn4 :regn4 :branch16))
(defop #x35 :if-ge (first second branch) 22t (:regn4 :regn4 :branch16))
(defop #x36 :if-gt (first second branch) 22t (:regn4 :regn4 :branch16))
(defop #x37 :if-le (first second branch) 22t (:regn4 :regn4 :branch16))

(defop #x38 :if-eqz (reg branch) 21t (:regn8 :branch16))
(defop #x39 :if-nez (reg branch) 21t (:regn8 :branch16))
(defop #x3a :if-ltz (reg branch) 21t (:regn8 :branch16))
(defop #x3b :if-gez (reg branch) 21t (:regn8 :branch16))
(defop #x3c :if-gtz (reg branch) 21t (:regn8 :branch16))
(defop #x3d :if-lez (reg branch) 21t (:regn8 :branch16))


(defop #x3e :unused () 10x ())
(defop #x3f :unused () 10x ())
(defop #x40 :unused () 10x ())
(defop #x41 :unused () 10x ())
(defop #x42 :unused () 10x ())
(defop #x43 :unused () 10x ())

(defop #x44 :aget         (dest array index) 23x (:regn8 :rega8 :regn8))
(defop #x45 :aget-wide    (dest array index) 23x (:regp8 :rega8 :regn8))
(defop #x46 :aget-object  (dest array index) 23x (:rego8 :rega8 :regn8))
(defop #x47 :aget-boolean (dest array index) 23x (:regn8 :rega8 :regn8))
(defop #x48 :aget-byte    (dest array index) 23x (:regn8 :rega8 :regn8))
(defop #x49 :aget-char    (dest array index) 23x (:regn8 :rega8 :regn8))
(defop #x4a :aget-short   (dest array index) 23x (:regn8 :rega8 :regn8))

(defop #x4b :aput         (src array index) 23x (:regn8 :rega8 :regn8))
(defop #x4c :aput-wide    (src array index) 23x (:regp8 :rega8 :regn8))
(defop #x4d :aput-object  (src array index) 23x (:rego8 :rega8 :regn8))
(defop #x4e :aput-boolean (src array index) 23x (:regn8 :rega8 :regn8))
(defop #x4f :aput-byte    (src array index) 23x (:regn8 :rega8 :regn8))
(defop #x50 :aput-char    (src array index) 23x (:regn8 :rega8 :regn8))
(defop #x51 :aput-short   (src array index) 23x (:regn8 :rega8 :regn8))

(defop #x52 :iget         (dest object field) 22c (:regn4 :rego4 :field))
(defop #x53 :iget-wide    (dest object field) 22c (:regp4 :rego4 :field))
(defop #x54 :iget-object  (dest object field) 22c (:rego4 :rego4 :field))
(defop #x55 :iget-boolean (dest object field) 22c (:regn4 :rego4 :field))
(defop #x56 :iget-byte    (dest object field) 22c (:regn4 :rego4 :field))
(defop #x57 :iget-char    (dest object field) 22c (:regn4 :rego4 :field))
(defop #x58 :iget-short   (dest object field) 22c (:regn4 :rego4 :field))

(defop #x59 :iput         (src object field) 22c (:regn4 :rego4 :field))
(defop #x5a :iput-wide    (src object field) 22c (:regp4 :rego4 :field))
(defop #x5b :iput-object  (src object field) 22c (:rego4 :rego4 :field))
(defop #x5c :iput-boolean (src object field) 22c (:regn4 :rego4 :field))
(defop #x5d :iput-byte    (src object field) 22c (:regn4 :rego4 :field))
(defop #x5e :iput-char    (src object field) 22c (:regn4 :rego4 :field))
(defop #x5f :iput-short   (src object field) 22c (:regn4 :rego4 :field))


(defop #x60 :sget         (dest field) 21c (:regn8 :field))
(defop #x61 :sget-wide    (dest field) 21c (:regp8 :field))
(defop #x62 :sget-object  (dest field) 21c (:rego8 :field))
(defop #x63 :sget-boolean (dest field) 21c (:regn8 :field))
(defop #x64 :sget-byte    (dest field) 21c (:regn8 :field))
(defop #x65 :sget-char    (dest field) 21c (:regn8 :field))
(defop #x66 :sget-short   (dest field) 21c (:regn8 :field))

(defop #x67 :sput         (src field) 21c (:regn8 :field))
(defop #x68 :sput-wide    (src field) 21c (:regp8 :field))
(defop #x69 :sput-object  (src field) 21c (:rego8 :field))
(defop #x6a :sput-boolean (src field) 21c (:regn8 :field))
(defop #x6b :sput-byte    (src field) 21c (:regn8 :field))
(defop #x6c :sput-char    (src field) 21c (:regn8 :field))
(defop #x6d :sput-short   (src field) 21c (:regn8 :field))

;; possibly these should be more specific about type of method?
(defop #x6e :invoke-virtual (method &rest) 35c
  (:method :reg4 :reg4 :reg4 :reg4 :reg4))
(defop #x6f :invoke-super (method &rest) 35c
  (:method :reg4 :reg4 :reg4 :reg4 :reg4))
(defop #x70 :invoke-direct (method &rest) 35c
  (:method :reg4 :reg4 :reg4 :reg4 :reg4))
(defop #x71 :invoke-static (method &rest) 35c
  (:method :reg4 :reg4 :reg4 :reg4 :reg4))
(defop #x72 :invoke-interface (method &rest) 35c
  (:method :reg4 :reg4 :reg4 :reg4 :reg4))

(defop #x73 :unused () 10xe ())

(defop #x74 :invoke-virtual/range (count method first-reg) 3rc
  (:lit8 :method :reg16))
(defop #x75 :invoke-super/range (count method first-reg) 3rc
  (:lit8 :method :reg16))
(defop #x76 :invoke-direct/range (count method first-reg) 3rc
  (:lit8 :method :reg16))
(defop #x77 :invoke-static/range (count method first-reg) 3rc
  (:lit8 :method :reg16))
(defop #x78 :invoke-interface/range (count method first-reg) 3rc
  (:lit8 :method :reg16))

(defop #x79 :unused () 10xe ())
(defop #x7a :unused () 10xe ())

(defop #x7b :neg-int (dest source) 12x (:regn4 :regn4))
(defop #x7c :not-int (dest source) 12x (:regn4 :regn4))
(defop #x7d :neg-long (dest source) 12x (:regp4 :regp4))
(defop #x7e :not-long (dest source) 12x (:regp4 :regp4))
(defop #x7f :neg-float (dest source) 12x (:regn4 :regn4))
(defop #x80 :neg-double (dest source) 12x (:regp4 :regp4))
(defop #x81 :int-to-long (dest source) 12x (:regp4 :regp4))
(defop #x82 :int-to-float (dest source) 12x (:regn4 :regn4))
(defop #x83 :int-to-double (dest source) 12x (:regp4 :regp4))
(defop #x84 :long-to-int (dest source) 12x (:regn4 :regn4))
(defop #x85 :long-to-float (dest source) 12x (:regn4 :regn4))
(defop #x86 :long-to-double (dest source) 12x (:regp4 :regp4))
(defop #x87 :float-to-int (dest source) 12x (:regn4 :regn4))
(defop #x88 :float-to-long (dest source) 12x (:regp4 :regp4))
(defop #x89 :float-to-double (dest source) 12x (:regp4 :regp4))
(defop #x8a :double-to-int (dest source) 12x (:regn4 :regn4))
(defop #x8b :double-to-long (dest source) 12x (:regp4 :regp4))
(defop #x8c :double-to-float (dest source) 12x (:regp4 :regp4))
(defop #x8d :int-to-byte (dest source) 12x (:regn4 :regn4))
(defop #x8e :int-to-char (dest source) 12x (:regn4 :regn4))
(defop #x8f :int-to-short (dest source) 12x (:regn4 :regn4))

(defop #x90 :add-int (dest source1 source2) 23x (:regn8 :regn8 :regn8))
(defop #x91 :sub-int (dest source1 source2) 23x (:regn8 :regn8 :regn8))
(defop #x92 :mul-int (dest source1 source2) 23x (:regn8 :regn8 :regn8))
(defop #x93 :div-int (dest source1 source2) 23x (:regn8 :regn8 :regn8))
(defop #x94 :rem-int (dest source1 source2) 23x (:regn8 :regn8 :regn8))
(defop #x95 :and-int (dest source1 source2) 23x (:regn8 :regn8 :regn8))
(defop #x96 :or-int (dest source1 source2) 23x (:regn8 :regn8 :regn8))
(defop #x97 :xor-int (dest source1 source2) 23x (:regn8 :regn8 :regn8))
(defop #x98 :shl-int (dest source1 source2) 23x (:regn8 :regn8 :regn8))
(defop #x99 :shr-int (dest source1 source2) 23x (:regn8 :regn8 :regn8))
(defop #x9a :ushr-int (dest source1 source2) 23x (:regn8 :regn8 :regn8))
(defop #x9b :add-long (dest source1 source2) 23x (:regp8 :regp8 :regp8))
(defop #x9c :sub-long (dest source1 source2) 23x (:regp8 :regp8 :regp8))
(defop #x9d :mul-long (dest source1 source2) 23x (:regp8 :regp8 :regp8))
(defop #x9e :div-long (dest source1 source2) 23x (:regp8 :regp8 :regp8))
(defop #x9f :rem-long (dest source1 source2) 23x (:regp8 :regp8 :regp8))
(defop #xa0 :and-long (dest source1 source2) 23x (:regp8 :regp8 :regp8))
(defop #xa1 :or-long (dest source1 source2) 23x (:regp8 :regp8 :regp8))
(defop #xa2 :xor-long (dest source1 source2) 23x (:regp8 :regp8 :regp8))
(defop #xa3 :shl-long (dest source1 source2) 23x (:regp8 :regp8 :regp8))
(defop #xa4 :shr-long (dest source1 source2) 23x (:regp8 :regp8 :regp8))
(defop #xa5 :ushr-long (dest source1 source2) 23x (:regp8 :regp8 :regp8))
(defop #xa6 :add-float (dest source1 source2) 23x (:regn8 :regn8 :regn8))
(defop #xa7 :sub-float (dest source1 source2) 23x (:regn8 :regn8 :regn8))
(defop #xa8 :mul-float (dest source1 source2) 23x (:regn8 :regn8 :regn8))
(defop #xa9 :div-float (dest source1 source2) 23x (:regn8 :regn8 :regn8))
(defop #xaa :rem-float (dest source1 source2) 23x (:regn8 :regn8 :regn8))
(defop #xab :add-double (dest source1 source2) 23x (:regp8 :regp8 :regp8))
(defop #xac :sub-double (dest source1 source2) 23x (:regp8 :regp8 :regp8))
(defop #xad :mul-double (dest source1 source2) 23x (:regp8 :regp8 :regp8))
(defop #xae :div-double (dest source1 source2) 23x (:regp8 :regp8 :regp8))
(defop #xaf :rem-double (dest source1 source2) 23x (:regp8 :regp8 :regp8)) 


(defop #xb0 :add-int/2addr (dest/src1 source2) 12x (:regn4 :regn4))
(defop #xb1 :sub-int/2addr (dest/src1 source2) 12x (:regn4 :regn4))
(defop #xb2 :mul-int/2addr (dest/src1 source2) 12x (:regn4 :regn4))
(defop #xb3 :div-int/2addr (dest/src1 source2) 12x (:regn4 :regn4))
(defop #xb4 :rem-int/2addr (dest/src1 source2) 12x (:regn4 :regn4))
(defop #xb5 :and-int/2addr (dest/src1 source2) 12x (:regn4 :regn4))
(defop #xb6 :or-int/2addr (dest/src1 source2) 12x (:regn4 :regn4))
(defop #xb7 :xor-int/2addr (dest/src1 source2) 12x (:regn4 :regn4))
(defop #xb8 :shl-int/2addr (dest/src1 source2) 12x (:regn4 :regn4))
(defop #xb9 :shr-int/2addr (dest/src1 source2) 12x (:regn4 :regn4))
(defop #xba :ushr-int/2addr (dest/src1 source2) 12x (:regn4 :regn4))
(defop #xbb :add-long/2addr (dest/src1 source2) 12x (:regp4 :regp4))
(defop #xbc :sub-long/2addr (dest/src1 source2) 12x (:regp4 :regp4))
(defop #xbd :mul-long/2addr (dest/src1 source2) 12x (:regp4 :regp4))
(defop #xbe :div-long/2addr (dest/src1 source2) 12x (:regp4 :regp4))
(defop #xbf :rem-long/2addr (dest/src1 source2) 12x (:regp4 :regp4))
(defop #xc0 :and-long/2addr (dest/src1 source2) 12x (:regp4 :regp4))
(defop #xc1 :or-long/2addr (dest/src1 source2) 12x (:regp4 :regp4))
(defop #xc2 :xor-long/2addr (dest/src1 source2) 12x (:regp4 :regp4))
(defop #xc3 :shl-long/2addr (dest/src1 source2) 12x (:regp4 :regp4))
(defop #xc4 :shr-long/2addr (dest/src1 source2) 12x (:regp4 :regp4))
(defop #xc5 :ushr-long/2addr (dest/src1 source2) 12x (:regp4 :regp4))
(defop #xc6 :add-float/2addr (dest/src1 source2) 12x (:regn4 :regn4))
(defop #xc7 :sub-float/2addr (dest/src1 source2) 12x (:regn4 :regn4))
(defop #xc8 :mul-float/2addr (dest/src1 source2) 12x (:regn4 :regn4))
(defop #xc9 :div-float/2addr (dest/src1 source2) 12x (:regn4 :regn4))
(defop #xca :rem-float/2addr (dest/src1 source2) 12x (:regn4 :regn4))
(defop #xcb :add-double/2addr (dest/src1 source2) 12x (:regp4 :regp4))
(defop #xcc :sub-double/2addr (dest/src1 source2) 12x (:regp4 :regp4))
(defop #xcd :mul-double/2addr (dest/src1 source2) 12x (:regp4 :regp4))
(defop #xce :div-double/2addr (dest/src1 source2) 12x (:regp4 :regp4))
(defop #xcf :rem-double/2addr (dest/src1 source2) 12x (:regp4 :regp4))

(defop #xd0 :add-int/lit16 (dest source const) 22s (:regn4 :regn4 :lit16))
(defop #xd1 :rsub-int/lit16 (dest source const) 22s (:regn4 :regn4 :lit16))
(defop #xd2 :mul-int/lit16 (dest source const) 22s (:regn4 :regn4 :lit16))
(defop #xd3 :div-int/lit16 (dest source const) 22s (:regn4 :regn4 :lit16))
(defop #xd4 :rem-int/lit16 (dest source const) 22s (:regn4 :regn4 :lit16))
(defop #xd5 :and-int/lit16 (dest source const) 22s (:regn4 :regn4 :lit16))
(defop #xd6 :or-int/lit16 (dest source const) 22s (:regn4 :regn4 :lit16))
(defop #xd7 :xor-int/lit16 (dest source const) 22s (:regn4 :regn4 :lit16))

(defop #xd8 :add-int/lit8 (dest source const) 22b (:regn8 :regn8 :lit8))
(defop #xd9 :rsub-int/lit8 (dest source const) 22b (:regn8 :regn8 :lit8))
(defop #xda :mul-int/lit8 (dest source const) 22b (:regn8 :regn8 :lit8))
(defop #xdb :div-int/lit8 (dest source const) 22b (:regn8 :regn8 :lit8))
(defop #xdc :rem-int/lit8 (dest source const) 22b (:regn8 :regn8 :lit8))
(defop #xdd :and-int/lit8 (dest source const) 22b (:regn8 :regn8 :lit8))
(defop #xde :or-int/lit8 (dest source const) 22b (:regn8 :regn8 :lit8))
(defop #xdf :xor-int/lit8 (dest source const) 22b (:regn8 :regn8 :lit8))
(defop #xe0 :shr-int/lit8 (dest source const) 22b (:regn8 :regn8 :lit8))
(defop #xe1 :shl-int/lit8 (dest source const) 22b (:regn8 :regn8 :lit8))
(defop #xe2 :ushr-int/lit8 (dest source const) 22b (:regn8 :regn8 :lit8))

(defop #xe3 :unused () 10xe ())
(defop #xe4 :unused () 10xe ())
(defop #xe5 :unused () 10xe ())
(defop #xe6 :unused () 10xe ())
(defop #xe7 :unused () 10xe ())
(defop #xe8 :unused () 10xe ())
(defop #xe9 :unused () 10xe ())
(defop #xea :unused () 10xe ())
(defop #xeb :unused () 10xe ())
(defop #xec :unused () 10xe ())
(defop #xed :unused () 10xe ())
(defop #xef :unused () 10xe ())
(defop #xf0 :unused () 10xe ())
(defop #xf1 :unused () 10xe ())
(defop #xf2 :unused () 10xe ())
(defop #xf3 :unused () 10xe ())
(defop #xf4 :unused () 10xe ())
(defop #xf5 :unused () 10xe ())
(defop #xf6 :unused () 10xe ())
(defop #xf7 :unused () 10xe ())
(defop #xf8 :unused () 10xe ())
(defop #xf9 :unused () 10xe ())

;; todo: new opcodes from ver 038+
(defop #xfa :unused () 10xe ()) ;; invoke-polymorphic
(defop #xfb :unused () 10xe ()) ;; invoke-polymorphic/range
(defop #xfc :unused () 10xe ()) ;; invoke-custom
(defop #xfd :unused () 10xe ()) ;; invoke-custom/range
(defop #xfe :unused () 10xe ()) ;; const-method-handle
(defop #xff :unused () 10xe ()) ;; const-method-type
;; dex ver 038+
#++
(defop #xfa :invoke-polymorphic
  (count method receiver reg1 reg2 reg3 reg4 prototype-ref)
  45cc
  ;; count is 4 bits, not sure if we need :lit4?
  ;; not sure if prototype-ref is just :type or something new?
  (:lit4 :method :rego16 :regn4 :regn4 :regn4 :regn4 :proto))
#++
(defop #xfb :invoke-polymorphic/range
  (count method receiver prototype-ref &rest)
  45cc
  ;; not sure if prototype-ref is just :type or something new?
  (:lit8 :method :rego16 :proto))


;;; pseudo-ops
(defmacro defop* (name args &key format types size write)
  `(progn
     (when (gethash ,name *opcodes*)
       (warn "redefining pseudo-opcode ~s (~s)~%"
             ',name (gethash ',name *opcodes*)))
     (setf (gethash ',name *opcodes*)
           (list :code NIL :name ',name :format ',format :args ',args
                 :types ',types
                 :size ,size
                 ;;:read ,read
                 :write ,write))))

(defop* :packed-switch-payload (&key first-key targets)
  ;; read handled by special case of :nop format
  :write (lambda (name op stream &key first-key targets)
           (declare (ignore name op))
           (flet ((out (x) (write-byte x stream)))
             (out #x0100)
             (out (word (length targets) 16))
             (out (ldb (byte 16 0) first-key))
             (out (ldb (byte 16 16) first-key))
             (loop for i across targets
                   do (out (ldb (byte 16 0) i))
                      (out (ldb (byte 16 16) i)))))
  :size (lambda (op &key first-key targets)
          (declare (ignore op first-key))
          (let ((s (+ 1 1 2 (* 2 (length targets))))) (values s s))))

(defop* :sparse-switch-payload (&key keys targets)
  ;; read handled by special case of :nop format
  :write (lambda (name op stream &key keys targets)
           (declare (ignore name op))
           (flet ((out (x) (write-byte x stream)))
             (out #x0200)
             (out (word (length targets) 16))
             (loop for i across keys
                   do (out (ldb (byte 16 0) i))
                      (out (ldb (byte 16 16) i)))
             (loop for i across targets
                   do (out (ldb (byte 16 0) i))
                      (out (ldb (byte 16 16) i)))))
  :size (lambda (op &key keys targets)
          (declare (ignore op))
          (let ((s (+ 1 1 (* 2 (length keys)) (* 2 (length targets)))))
            (values s s))))

(defop* :fill-array-data-payload (&key element-width data)
  ;; read handled by special case of :nop format
  :write (lambda (name op stream &key element-width data)
           (declare (ignore name op))
           (flet ((out (x) (write-byte x stream)))
             (out #x0300)
             (out (word element-width 16))
             (out (ldb (byte 16 0) (length data)))
             (out (ldb (byte 16 16) (length data)))
             ;; not sure if arbitrary octet sizes are allowed or not
             ;; only handling 1 and multiples of 2 for now though...
             (assert (or (= element-width 1)
                         (evenp element-width)))
             (if (= element-width 1)
                 (loop for i below (length data) by 2
                       do (out (word (if (array-in-bounds-p data (1+ i))
                                         (aref data (1+ i))
                                         0) 8
                                     (aref data i) 8)))
                 (loop for i across data
                       do (loop for o below (floor element-width 2)
                                do (out (ldb (byte 16 (* o 16)) i)))))))
  :size (lambda (op &key element-width data)
          (declare (ignore op))
          (let ((s (+ 1 1 2 (floor (1+ (* (length data) element-width))
                                   2))))
            (values s s))))

(defop* :label (name)
  :write (lambda (&rest r) (declare (ignore r)))
  :size (lambda (op name) (declare (ignore op name)) (values 0 0)))

;;; disassembler passes
(defun expand-string/type/etc-refs (asm)
  ;; look up string/type/etc indices in the .dex file's tables if available
  (labels ((fix-method (m)
             ;; we can't just use class + method names, since might
             ;; have 2 with same name and different signatures...
             m #++(list (first m) (third m)))
           (fix-field (f)
             ;; class, name, type
             (list (first f) (third f) (second f)))
           (lookup (type value)
             (case type
               (:string
                   (if (boundp '*strings*) (aref *strings* value) value))
                  ((:type :array :class)
                   (if (boundp '*types*) (aref *types* value) value))
                  (:method
                      (if (boundp '*methods*)
                          (fix-method (aref *methods* value))
                          value))
                  (:field
                   (if (boundp '*fields*)
                       (fix-field (aref *fields* value))
                       value))
                  (t value))))
    (loop for (op . args) in asm
          for types = (getf (gethash op *opcodes*)
                            :types)
          collect
          (cons op
                (loop for arg in args
                      for i from 0
                      for type = (nth i types)
                      collect (lookup type arg))))))

(defun add-labels (asm)
  ;; convert branch offsets to labels, and add labels to code

  (let ((branches (make-hash-table))
        (name-counters (make-hash-table))
        ;; (cons->address and address->cons)
        (addresses (make-hash-table)))
    ;; we do this in 3 passes just to keep things simpler, since switch
    ;; ops need to dereference twice to get actual destination addresses
    ;; (and there doesn't seem to be anything in the spec preventing 2
    ;;  switches from sharing an offset table)

    ;; calculate PC of each instruction
    ;; - probably should have tracked this when originally decoding the
    ;;   bytecode, but there isn't really anywhere convenient to store it
    (flet ((align (op value)
             ;; fixme: make this configurable
             (if (member op '(:packed-switch-payload :sparse-switch-payload
                              :fill-array-data-payload))
                 ;; nop tables are aligned to even instructions...
                 (+ value (logand value 1))
                 value)))
      (loop for pc = 0 then (+ pc (apply (getf (gethash op *opcodes*) :size)
                                         ins))
            for ins in asm
            for op = (car ins)
            do (setf pc (align op pc))
               (setf (gethash ins addresses) pc
                     (gethash pc addresses) ins)))

    ;; loop through instructions, finding branches, and calculating dest
    (labels ((add-branch (type dest &optional index2)
               (let* ((index (incf (gethash type name-counters 0)))
                      (name (make-symbol (format nil "~a-~a~@[-~a~]"
                                                 type index index2))))
                 (setf (gethash dest branches) name)))
             (add-switch (type base targets)
               (loop for i from 0
                     for off across targets
                     do (add-branch type (+ base off) i))))
      (loop for ins in asm
            for pc = (gethash ins addresses)
            for (op . arg) = ins
            do (case op
                 (:packed-switch
                  (let ((table (gethash (+ pc (second arg)) addresses)))
                    (check-type table (cons (eql :packed-switch-payload)))
                    (add-switch op pc (getf (cdr table) :targets))))
                 (:sparse-switch
                  (let ((table (gethash (+ pc (second arg)) addresses)))
                    (check-type table (cons (eql :sparse-switch-payload)))
                    (add-switch op pc (getf (cdr table) :targets))))
                 ((:goto :goto/16 :goto/32)
                  (add-branch :goto (+ pc (first arg))))
                 ((:if-eq :if-ne :if-lt :if-le :if-gt :if-ge)
                  (add-branch op (+ pc (third arg))))
                 ((:if-eqz :if-nez :if-ltz :if-lez :if-gtz :if-gez)
                  (add-branch op (+ pc (second arg)))))))

    ;; finally, add labels and replace branch offsets, and extract jump tables
    ;; and array tables
    (loop for remaining on asm
          for ins = (car remaining)
          for pc = (gethash ins addresses)
          for (op . arg) = ins
          for label = (gethash pc branches)
          when label
            collect (list :label label)
          when (case op
                 (:nop
                  ;; assume :nop before a nop-table is just padding and drop it
                  (unless (member (caadr remaining)
                                  '(:fill-array-data-payload
                                    :sparse-switch-payload
                                    :packed-switch-payload))
                    ins))
                 (:fill-array
                  (let ((table (gethash (+ pc (second arg)) addresses)))
                    (list* :fill-array  (first arg) (cdr table))))
                 ((:fill-array-data-payload
                   :packed-switch-payload :sparse-switch-payload)
                  nil)
                 (:packed-switch
                  (let ((table (gethash (+ pc (second arg)) addresses)))
                    (list
                     :packed-switch (first arg)
                     (loop for key from (getf (cdr table) :first-key)
                           for off across (getf (cdr table) :targets)
                           collect (cons key (gethash (+ pc off) branches))))))
                 (:sparse-switch
                  (let ((table (gethash (+ pc (second arg)) addresses)))
                    (list
                     :sparse-switch (first arg)
                     (loop for key across (getf (cdr table) :keys)
                           for off across (getf (cdr table) :targets)
                           collect (cons key (gethash (+ pc off) branches))))))
                 ((:goto :goto/16 :goto/32)
                  (list :goto (gethash (+ pc (first arg)) branches)))
                 ((:if-eq :if-ne :if-lt :if-le :if-gt :if-ge)
                  (list op (first arg) (second arg)
                        (gethash (+ pc (third arg)) branches)))
                 ((:if-eqz :if-nez :if-ltz :if-lez :if-gtz :if-gez)
                  (list op (first arg)
                        (gethash (+ pc (second arg)) branches)))
                 (t ins))
            collect it)))

(alexandria:define-constant +2addr-opcodes+
    '((:add-int/2addr . :add-int)
      (:sub-int/2addr . :sub-int)
      (:mul-int/2addr . :mul-int)
      (:div-int/2addr . :div-int)
      (:rem-int/2addr . :rem-int)
      (:and-int/2addr . :and-int)
      (:or-int/2addr . :or-int)
      (:xor-int/2addr . :xor-int)
      (:shl-int/2addr . :shl-int)
      (:shr-int/2addr . :shr-int)
      (:ushr-int/2addr . :ushr-int)
      (:add-long/2addr . :add-long)
      (:sub-long/2addr . :sub-long)
      (:mul-long/2addr . :mul-long)
      (:div-long/2addr . :div-long)
      (:rem-long/2addr . :rem-long)
      (:and-long/2addr . :and-long)
      (:or-long/2addr . :or-long)
      (:xor-long/2addr . :xor-long)
      (:shl-long/2addr . :shl-long)
      (:shr-long/2addr . :shr-long)
      (:ushr-long/2addr . :ushr-long)
      (:add-float/2addr . :add-float)
      (:sub-float/2addr . :sub-float)
      (:mul-float/2addr . :mul-float)
      (:div-float/2addr . :div-float)
      (:rem-float/2addr . :rem-float)
      (:add-double/2addr . :add-double)
      (:sub-double/2addr . :sub-double)
      (:mul-double/2addr . :mul-double)
      (:div-double/2addr . :div-double)
      (:rem-double/2addr . :rem-double))
  :test 'equal)

(defparameter *2addr-map*
  (alexandria:alist-hash-table (loop for (a . b) in +2addr-opcodes+
                                     collect (cons a b)
                                     collect (cons b a))))
(defun use-generic-opcodes (asm)
  ;; convert things like const/4 to just const
  (loop for ins in asm
        for (op . arg) = ins
        collect
        (case op
          ;; not sure if we can combine move and move-wide easily
          ;; and combining move-object would require type inference
          ;; in the assembler, so leaving separate for now...
          ((:move/from16 :move/16)
           (cons :move arg))
          ((:move-wide/from16 :move-wide/16)
           (cons :move-wide arg))
          ((:move-object/from16 :move-object/16)
           (cons :move-object arg))
          ((:const/4 :const/16 :const/high16)
           (cons :const arg))
          ((:const-wide/16 :const-wide/32 :const-wide/high16)
           (cons :const-wide arg))
          ((:const-string :const-string/jumbo)
           (cons :const-string arg))
          ((:goto/16 :goto/32)
           (cons :goto arg))
          ;; possibly should combine packed/sparse switch?
          ;; (assuming previous pass expanded them to both have a list
          ;;  of keys and targets)
          #++((:packed-switch :sparse-switch)
              (cons :switch arg))
          (#.(mapcar 'car +2addr-opcodes+)
           (list (gethash op *2addr-map*)
                 (first arg) (first arg) (second arg)))

          ;; not sure if it is reasonable to merge /lit16 and /lit8 ops
          ;; since neither is a superset of the other (reg size vs
          ;; size of constant)
          (t ins))))

;; todo: pass to verify all branches/switches have valid labels?
(defparameter *disassembler-passes* '(expand-string/type/etc-refs
                                      add-labels
                                      use-generic-opcodes))

(defun unassemble (code &key (passes *disassembler-passes*))
  (loop with asm
          = (flex:with-input-from-sequence (s code)
              (loop for instruction = (read-byte s nil)
                    for op = (when instruction (ldb (byte 8 0) instruction))
                    for opdef = (when op (gethash (aref *opcode-index* op)
                                                  *opcodes*))
                    for op-name = (getf opdef :name)
                    for reader = (getf opdef :read)
                    while instruction
                    collect (funcall reader op-name instruction s)))
        for pass in passes
        do (setf asm (funcall pass asm))
        finally (return asm)))


#++
(unassemble #(26 2536 4209 1403 0 14))

(defun asm-lookup-constants (asm)
  (flet ((lookup (type value)
           (case type
             (:string
              (if (boundp '*strings*) (gethash value *strings* value) value))
             ((:type :array :class)
              (unless (gethash value *types*)
                (break "failed to lookup ~s ~s?" type value))
              (if (boundp '*types*) (gethash value *types* value) value))
             (:method
              (unless (gethash value *methods*)
                (break "failed to lookup ~s ~s?" type value *methods*))
                 (if (boundp '*methods*) (gethash value *methods* value) value))
             (:field
              (unless (gethash value *fields*)
                (break "failed to lookup ~s ~s?" type value *fields*) )
              (if (boundp '*fields*) (gethash value *fields* value) value))
             (t value))))
    (loop for (op . args) in asm
          for types = (getf (gethash op *opcodes*) :types)
          collect (cons op
                        (loop for arg in args
                              for i from 0
                              for type = (nth i types)
                              collect (lookup type arg))))))

(defun asm-select-sized-opcode (asm)
  (flet ((u4p (x) (typep x '(unsigned-byte 4)))
         (u8p (x) (typep x '(unsigned-byte 8)))
         (u16p (x) (typep x '(unsigned-byte 16)))
         (u32p (x) (typep x '(unsigned-byte 32)))
         #++(u64p (x) (typep x '(unsigned-byte 64)))
         (s4p (x) (typep x '(signed-byte 4)))
         #++(s8p (x) (typep x '(signed-byte 8)))
         (s16p (x) (typep x '(signed-byte 16)))
         (s32p (x) (typep x '(signed-byte 32)))
         (s64p (x) (typep x '(signed-byte 64)))
         (cant-encode (x &optional reason)
           (error "can't encode ~s~@[, ~s~]" x reason)))
    (loop with from16 = (alexandria:alist-hash-table
                         '((:move . :move/from16)
                           (:move-wide . :move-wide/from16)
                           (:move-object . :move-object/from16)))
          with arg16 = (alexandria:alist-hash-table
                        '((:move . :move/16)
                          (:move-wide . :move-wide/16)
                          (:move-object . :move-object/16)))
          for ins in asm
          for (op . arg) = ins
          collect
          (case op
            ((:move :move-wide :move-object)
             (cond
               ((and (u4p (first arg)) (u4p (second arg)))
                ins)
               ((and (u8p (first arg)) (u16p (second arg)))
                (cons (gethash op from16) arg))
               ((and (u16p (first arg)) (u16p (second arg)))
                (cons (gethash op arg16) arg))
               (t (cant-encode ins "invalid register indices"))))
            (:const
             (cond
               ((and (u4p (first arg)) (s4p (second arg)))
                (cons :const/4 arg))
               ((and (u8p (first arg)) (s16p (second arg)))
                (cons :const/16 arg))
               ((and (u8p (first arg)) (s32p (second arg))
                     (zerop (ldb (byte 16 0) (second arg))))
                (cons :const/high16 arg))
               ((and (u8p (first arg)) (s32p (second arg)))
                (cons :const arg))
               ;; we can also encode single-float or unsigned int,
               ;; though we won't decode them properly
               ((and (u8p (first arg)) (u32p (second arg)))
                (cons :const arg))
               ((and (u8p (first arg)) (typep (second arg) 'single-float))
                (cons :const arg))
               (t (cant-encode ins "invalid register index or immediate value too large"))))
            (:const-wide
             (cond
               ((and (u8p (first arg)) (s16p (second arg)))
                (cons :const-wide/16 arg))
               ((and (u8p (first arg)) (s32p (second arg)))
                (cons :const-wide/32 arg))
               ((and (u8p (first arg)) (s64p (second arg))
                     (zerop (ldb (byte 48 0) (second arg))))
                (cons :const-wide/high16 arg))
               ((and (u8p (first arg)) (s64p (second arg)))
                (cons :const-wide arg))
               (t (cant-encode ins "invalid register index or immediate value too large"))))

            (:const-string
             (cond
               ((u16p (second arg))
                (cons :const-string arg))
               ((u32p (second arg))
                (cons :const-string/jumbo arg))
               (t (cant-encode ins "invalid string-table index"))))
            ;; we can't expand :goto yet, because we don't know here
            ;; the jump goes until we assign specific instructions
            (#.(mapcar 'cdr +2addr-opcodes+)
             ;; use /2addr version when src1 nd dest are same, and both are u4
             (if (and (= (first arg) (second arg))
                      (u4p (first arg)) (u4p (third arg)))
                 (cons (gethash op *2addr-map*) (cdr arg))
                 ins))

            ;; not sure if it is reasonable to merge /lit16 and /lit8 ops
            ;; since neither is a superset of the other (reg size vs
            ;; size of constant)
            (t ins)))))

(defun asm-finalize-branches (asm)
  ;; first pass: find min/max possible address for every label,goto
  (flet ((s8p (x) (typep x '(signed-byte 8)))
         (s16p (x) (typep x '(signed-byte 16)))
         (s32p (x) (typep x '(signed-byte 16)))
         #++(ilmax (&rest r)
              (reduce (lambda (a b)
                        (if (>= (integer-length a) (integer-length b)) a b))
                      r))
         (ilmax (a b)
           (if (>= (integer-length a) (integer-length b)) a b)))
    (let ((labels (make-hash-table)))
      (loop with min = 0
            with max = 0
            for instruction in asm
            for (name . arg) = instruction
            for opdef = (gethash name *opcodes*)
            for size = (getf opdef :size)
            ;; everything else should have a fixed size by now,
            ;; just need to handle GOTO by hand
            when (eq name :goto)
              do (incf min 1) (incf max 3)
            else
              do (multiple-value-bind (omin omax) (apply size instruction)
                   (incf min omin)
                   (incf max omax))
            when (eq name :label)
              do (setf (gethash (first arg) labels) (list min max)))

      ;; second pass: assign instructions to GOTOs, update labels with
      ;; actual addresses
      (setf asm
            (loop with pc = 0
                  for instruction in asm
                  for (name . arg) = instruction
                  for opdef = (gethash name *opcodes*)
                  for size = (getf opdef :size)
                  ;; everything else should have a fixed size by now,
                  ;; just need to handle GOTO by hand
                  when (eq name :label)
                    do (setf (gethash (first arg) labels) (list pc pc))
                  when (eq name :goto)
                    collect (destructuring-bind (lmin lmax)
                                (gethash (first arg) labels)
                              (let ((d (ilmax (- lmin pc) (- lmax pc))))
                                (cond
                                  ((s8p d) (incf pc 1) instruction)
                                  ((s16p d) (incf pc 2) (cons :goto/16 arg))
                                  ((s32p d) (incf pc 3) (cons :goto/32 arg))
                                  ;; invalid, let final pass deal with it
                                  (t instruction))))
                  else
                    do (incf pc (apply size instruction))
                    and collect instruction))
      ;; 3rd pass: assign addresses, store refs to array/switch instructions
      ;; build tables for array/switches, add to end and update array/switches
      (let ((tables nil)
            (pc 0))
        (append
         (loop for instruction in asm
               for (name . arg) = instruction
               for opdef = (gethash name *opcodes*)
               for size = (getf opdef :size)
               ;; labels should have correct locations from previous pass
               ;; so calculate offsets and update goto/branch instructions
               collect
               (flet ((off (x)
                        (- (first (gethash x labels)) pc)))
                 (case name
                   ((:goto :goto/16 :goto/32)
                    (list name (off (first arg))))
                   ((:if-eq :if-ne :if-lt :if-gt :if-le :if-ge)
                    (list name (first arg) (second arg)
                          (off (third arg))))
                   ((:if-eqz :if-nez :if-ltz :if-gtz :if-lez :if-gez)
                    (list name (first arg)
                          (off (second arg))))
                   (:fill-array
                    ;; make a copy of the instruction so we can patch it later
                    (let ((i (copy-list instruction)))
                      (push (list pc i) tables)
                      i))
                   ((:packed-switch :sparse-switch)
                    ;; make a copy of the instruction so we can patch it later
                    (let ((i (list name (first arg)
                                   (loop for (k . label) in (second arg)
                                         collect (cons k (off label))))))
                      (push (list pc i) tables)
                      i))
                   (t instruction)))
               do (incf pc (apply size instruction)))
         (loop for (from instruction) in (reverse tables)
               for (op . args) = instruction
               when (oddp pc)
                 do (incf pc) ;; align pc if needed
                 and collect '(:nop)
               collect
               (progn
                 (case op
                   (:fill-array
                    (destructuring-bind (&key element-width data) (cdr args)
                      (setf (cddr instruction) (list (- pc from)))
                      (let ((new (list :fill-array-data-payload
                                       :element-width element-width
                                       :data data)))
                        (incf pc (apply (getf (gethash (car new) *opcodes*)
                                              :size)
                                        new))
                        new)))
                   (:packed-switch
                    (let ((targets (second args)))
                      (setf (third instruction) (- pc from))
                      (let ((new (list :packed-switch-payload
                                       :first-key (caar targets)
                                       :targets (map 'vector 'cdr targets))))
                        (incf pc (apply (getf (gethash (car new) *opcodes*)
                                              :size)
                                        new))
                        new)))
                   (:sparse-switch
                    (let ((targets (second args)))
                      (setf (third instruction) (- pc from))
                      (let ((new (list :sparse-switch-payload
                                       :keys (map 'vector 'car targets)
                                       :targets (map 'vector 'cdr targets))))
                        (incf pc (apply (getf (gethash (car new) *opcodes*)
                                              :size)
                                        new))
                        new)))))))))))

(defparameter *assembler-passes* '(asm-lookup-constants
                                   asm-select-sized-opcode
                                   asm-finalize-branches))

(defun assemble (asm &key (passes *assembler-passes*))
  (loop for pass in passes
        do (setf asm (funcall pass asm)))
  (flex:with-output-to-sequence (out :element-type '(unsigned-byte 16))
    (loop for instruction in asm
          for (name . args) = instruction
          for opdef = (gethash name *opcodes*)
          for opcode = (getf opdef :code)
          for format = (getf opdef :format)
          for writer = (getf opdef :write)
          collect (if writer
                      (apply writer name opcode out args)
                      (error "don't know how to assemble opcode ~s" name)))))


#++
(assemble (unassemble #(26 2536 4209 1403 0 14)))
#++
(let ((*disassembler-passes* nil))
  (unassemble (assemble '((:CONST-STRING 0 2536) (:INVOKE-STATIC 1403 0)  (:const 1 1) (:RETURN 1)))))
#++
(let ((*strings* (alexandria:alist-hash-table '(("loadLibrary" . 0)
                                                ("Ljava/lang/System;" . 1)
                                                ("testing" . 2))
                                              :test 'equal))
      (*methods* (alexandria:alist-hash-table
                  '((("Ljava/lang/System;" "loadLibrary") . 0))
                  :test 'equal)))
  (assemble '((:CONST-STRING 0 "testing")
              (:INVOKE-STATIC ("Ljava/lang/System;" "loadLibrary") 0)
              (:const 1 1)
              (:RETURN 1))))


#++
(let ((*strings* (alexandria:alist-hash-table '(("loadLibrary" . 0)
                                                ("Ljava/lang/System;" . 1)
                                                ("testing" . 2))
                                              :test 'equal))
      (*methods* (alexandria:alist-hash-table
                  '((("Ljava/lang/System;" "loadLibrary") . 0))
                  :test 'equal)))
  (assemble '((:label foo)
              (:CONST-STRING 0 "testing")
              (:label foo2)
              (:if-eq 0 2 foo)
              (:INVOKE-STATIC ("Ljava/lang/System;" "loadLibrary") 0)
              (:label bar)
              (:goto end)
              (:const 1 1)
              (:sparse-switch 2 ((7 . foo) (9 . foo2) (11 . foo) (12 . end)))
              (:goto bar)
              (:label end)
              (:RETURN 1))))

#++
(let ((*strings* (vector "loadLibrary" "Ljava/lang/System;" "testing"
                         :test 'equal))
      (*methods* (vector '("Ljava/lang/System;" "loadLibrary"))))
  (unassemble
   #(26 2 8242 65534 4209 0 0 1576 4370 556 5 0 64296 271 512 4 7 0 9 0
     11 0 12 0 65527 65535 65529 65535 65527 65535 4 0)))


