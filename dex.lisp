(in-package #:3b-dex)

;; writer will refuse to write any format not in this list
(defparameter *supported-formats* '(35))
;; default version number to use in header
(defparameter *default-format* 35)

(defconstant +no-index+ #.(1- (expt 2 32))) ; #xffffffff
(defconstant +dex-endian-constant+ #x12345678)
(defconstant +dex-reverse-endian-constant+ #x78563412)


(defun dex-magic (version)
  (check-type version (integer 0 999))
  (ub8-vector :length 8
              :contents (list #x64 #x65 #x78 #x0a
                              (+ #x30 (floor version 100))
                              (+ #x30 (mod (floor version 10) 10))
                              (+ #x30 (mod version 10))
                              #x00)))

(defun check-dex-magic (magic)
  (flet ((dex-version (m)
           (loop for i from 4 below 7
                 for x = 100 then (floor x 10)
                 for digit = (- (elt m i) #x30)
                 when (not (<= 0 digit 9))
                   do (return-from dex-version nil)
                 sum (* digit x))))
    (and (= (length magic) 8)
         (not (mismatch magic #(#x64 #x65 #x78 #x0a) :end1 4))
         (= (elt magic 7) 0)
         (dex-version magic))))


#++(check-dex-magic (dex-magic 35))


;; *leb128 are always 32bit in .dex
(defun read-uleb128 (stream)
  (loop with s = 0
        for i below 5
        for b = (read-byte stream)
        do (setf s (dpb b (byte 7 (* i 7)) s))
        while (logbitp 7 b)
        finally (return s)))

(defun read-uleb128+1 (stream)
  (1- (read-uleb128 stream)))

(defun read-sleb128 (stream)
  ;; can't just call read-uleb128, since we need to sign extend from last
  ;; octet in the encoding
  (let ((b (loop with s = 0
                 with sign = nil
                 for i below 5
                 for b = (or sign (read-byte stream))
                 do (setf s (dpb b (byte 7 (* i 7)) s))
                 unless (logbitp 7 b)
                   do (setf sign (if (logbitp 6 b) #xff #x00))
                 finally (return s))))
    (if (< b #.(expt 2 31))
        b
        (dpb b (byte 31 0) -1))))

#++
(flex:with-input-from-sequence (s #(0 1 #x7f #x80 #x7f))
  (list (read-uleb128 s) (read-uleb128 s) (read-uleb128 s) (read-uleb128 s))
  #++(loop for a = (ignore-errors (read-uleb128 s)) while a collect a))
#++
(flex:with-input-from-sequence (s #(0 1 #x7f #x80 #x7f))
  (loop for a = (ignore-errors (read-uleb128+1 s)) while a collect a))
#++
(flex:with-input-from-sequence (s #(0 1 #x7f #x80 #x7f))
  (loop for a = (ignore-errors (read-sleb128 s)) while a collect a))



(defun decode-mutf8 (octets &key decoded-length)
  (declare (optimize speed)
           (type (array (unsigned-byte 8) (*)) octets))
  (let ((o (if decoded-length
               (make-array decoded-length :element-type '(unsigned-byte 16)
                                          :fill-pointer 0)
               (make-array 1 :element-type '(unsigned-byte 16)
                             :fill-pointer 0 :adjustable t))))
    ;; todo: better errors
    (loop with partial of-type (unsigned-byte 32) = 0
          with remaining of-type (integer 0 4) = 0
          for i across octets
          do
             (if (logbitp 7 i)
                  ;; multibyte
                 (cond
                   ((and (= (ldb (byte 2 6) i) 2)
                         (plusp remaining))
                    ;; continuation
                    (setf partial (+ (ash partial 6) (ldb (byte 6 0) i)))
                    (decf remaining)
                    (when (zerop remaining)
                      (vector-push-extend partial o)))
                   ((and (= (ldb (byte 3 5) i) 6)
                         (zerop remaining))
                    ;; 2 byte
                    (setf remaining 1
                          partial (ldb (byte 6 0) i)))
                   ((and (= (ldb (byte 4 4) i) 14)
                         (zerop remaining))
                    ;; 3 byte
                    (setf remaining 2
                          partial (ldb (byte 5 0) i)))
                   (t ;; anything else is invalid
                    (error "invalid mutf-8 encoding at octet ~d of ~s" i octets)))
                 ;; single byte
                 (cond
                   ((not (zerop remaining))
                    (error "invalid mutf-8 encoding at octet ~d of ~s" i octets))
                   (t (vector-push-extend i o)))))
    o))

#++ (decode-mutf8 #(#xc2 #xa2)) ;#(162)
#++ (decode-mutf8 #(#xe2 #x82 #xac)) ;#(8364)

#++
(defparameter *all-flags* '((:public . #x01)
                            (:private . #x02)
                            (:protected . #x04)
                            (:static . #x08)
                            (:final . #x10)
                            (:synchronized . #x20)
                            (:volatile . #x40)
                            (:bridge . #x40)
                            (:transient . #x80)
                            (:varargs . #x80)
                            (:native . #x100)
                            (:interface . #x200)
                            (:abstract . #x400)
                            (:strict . #x800)
                            (:synthetic . #x1000)
                            (:annotation . #x2000)
                            (:enum . #x4000)
                            (:unused . #x8000)
                            (:constructor . #x10000)
                            (:declared-synchronized . #x20000)))

(defparameter *class-flags* '((:public . #x01)
                              (:private . #x02)
                              (:protected . #x04)
                              (:static . #x08)
                              (:final . #x10)
                              (:interface . #x200)
                              (:abstract . #x400)
                              (:synthetic . #x1000)
                              (:annotation . #x2000)
                              (:enum . #x4000)))

(defparameter *field-flags* '((:public . #x01)
                              (:private . #x02)
                              (:protected . #x04)
                              (:static . #x08)
                              (:final . #x10)
                              (:volatile . #x40)
                              (:transient . #x80)
                              (:synthetic . #x1000)
                              (:enum . #x4000)))

(defparameter *method-flags* '((:public . #x01)
                               (:private . #x02)
                               (:protected . #x04)
                               (:static . #x08)
                               (:final . #x10)
                               (:synchronized . #x20)
                               (:bridge . #x40)
                               (:varargs . #x80)
                               (:native . #x100)
                               (:abstract . #x400)
                               (:strict . #x800)
                               (:synthetic . #x1000)
                               (:constructor . #x10000)
                               (:declared-synchronized . #x20000)))

(defun decode-flags (flags mapping)
  (loop for (name . value) in mapping
        when (logtest value flags)
          collect name))

(defun encode-flags (flags mapping)
  (loop for name in flags
        sum (cdr (assoc name mapping))))

#++
(decode-flags (encode-flags '(:public :final :enum) *field-flags*)
              *field-flags*)

(defclass dex-annotation ()
  ((visibility :initarg :visibility :accessor visibility)
   (type :initarg :type :accessor annotation-type)
   (elements :initform (make-hash-table :test 'equal)
             :initarg :annotations :accessor elements)))

(defclass dex-class-field ()
  ;; not storing class name for now
  ((type :initarg :type :accessor field-type)
   (name :initarg :name :accessor name)
   (flags :initform () :initarg :flags :accessor flags)
   (annotations :initform nil :initarg :annotations :accessor annotations)))

(defclass dex-class-static-field (dex-class-field)
  ((value :initform nil :initarg :value :accessor value)))

(defclass dex-catch-handler ()
  ((handlers :initform nil :initarg :handlers :accessor handlers)
   (catch-all :initform nil :initarg :catch-all :accessor catch-all)))

(defclass dex-try-block ()
  ((start :initarg :start :accessor start)
   (count :initarg :count :accessor :instruction-count)
   (handlers :initarg :handlers :accessor handlers)))


(defclass dex-debug-info ()
  ((start :initarg :start :accessor start)
   (parameters :initarg :parameters :accessor parameters)
   (bytecode :initarg :bytecode :accessor bytecode)))


(defclass dex-code ()
  (;;number of registers
   (registers :initarg :registers :accessor registers)
   ;; number of words of incoming args
   (ins :initarg :ins :accessor ins)
   ;; # of words of outgoing args
   (outs :initarg :outs :accessor outs)
   ;; sequence of 'try' block definitions, including catch handlers
   (tries :initarg :tries :accessor tries)
   (debug-info :initarg :debug-info :accessor debug-info)
   ;; sequence of u16 instructions
   (instructions :initarg :instructions :accessor instructions)))

(defclass dex-class-method ()
  ;; not storing class for now
  ;; not storing 'shorty' version of prototype info for now...
  ((return-tytpe :initarg :return-type :accessor return-type)
   ;; sequence? of types
   (parameters :initarg :parameters :accessor parameters)
   (name :initarg :name :accessor name)
   (flags :initform () :initarg :flags :accessor flags)
   (code :initform nil :initarg :code :accessor code)
   (annotations :initform nil :initarg :annotations :accessor annotations)
   ;; if not NIL, sequence of NILs or vectors of annotations for corresponding
   ;; elements in PARAMETERS
   (parameter-annotations :initform nil :initarg :parameter-annotations
                          :accessor parameter-annotations)))



(defclass dex-class ()
  ;; not sure if we should store types as names or actual instances?
  ;; (in superclass, interfaces, etc)
  ((type-name :initarg :type-name :accessor type-name)
   ;; flags = list of keywords from *class-flags*
   (flags :initform () :initarg :flags :accessor flags)
   ;; superclass = NIL or superclass type
   (superclass :initform nil :initarg :superclass :accessor superclass)
   ;; sequence? of interface types
   (interfaces :initform nil :initarg :interfaces :accessor interfaces)
   ;; name of source file, or NIL
   (source-file :initform nil :initarg :source-file :accessor source-file)
   ;; sequence? of dex-annotation instances
   (annotations :initform nil :initarg :annotations :accessor annotations)
   ;; sequence?s of field/method definitions
   (static-fields :initform nil :initarg :static-fields :accessor static-fields)
   (instance-fields :initform nil
                    :initarg :instance-fields :accessor instance-fields)
   (direct-methods :initform nil
                   :initarg :direct-methods :accessor direct-methods)
   (virtual-methods :initform nil
                    :initarg :virtual-methods :accessor virtual-methods)))

(defclass dex-file ()
  ((version :initform *default-format* :initarg :version :accessor version)
   (endian :initform :le :initarg :endian :accessor endian)
   (link-table :initarg :link-table :accessor link-table)
   (classes :initarg :classes :accessor classes)
   ;; probably drop the rest of these once classes deserialize and serialize
   ;; properly?
   (maps :initarg :maps :accessor map-list)
   (strings :initarg :strings :accessor strings)
   (types :initarg :types :accessor types)
   (prototypes :initarg :prototypes :accessor prototypes)
   (fields :initarg :fields :accessor fields)
   (methods :initarg :methods :accessor methods)
   (data :initarg :data :accessor data)))



(defun read-link-table (stream count start)
  (when (plusp count)
    (let ((a (make-array count)))
      a)))


(defun read-string-data-item (stream)
  ;; stores size of the 'decoded' utf-16 string, still have to read by octets
  ;; to find end of 'mutf8' encoded string :/
  (let* ((size (read-uleb128 stream))
         (encoded (read-zero-terminated stream size))
         (raw-16 (decode-mutf8 encoded :decoded-length size))
         (string (ignore-errors (map 'string 'code-char raw-16))))
    ;; string is allowed to decode to invalid utf16, so return a string if we
    ;; can decode it, otherwise a ub16 array
    (values (or string raw-16) size)))

(defun read-strings (stream count start)
  (when (plusp count)
    (file-position stream start)
    (let ((a (make-array count)))
      ;; read offsets from string_id table
      (loop for i below count
            do (setf (aref a i) (read-u32 stream)))
      ;; then replace replace the offsets with actual strings from data area
      ;; probably would be nicer to avoid all the seeking here, but
      ;; too lazy for now...
      (loop for i from 0
            for offset across a
            do (file-position stream offset)
               (setf (aref a i) (read-string-data-item stream)))
      a)))

(defun read-types (stream count start strings)
  (when (plusp count)
    (file-position stream start)
    (let ((a (make-array count)))
      ;; table is list of indices into string table
      ;; possibly should decode strings into more friendly format?
      (loop for i below count
            do (setf (aref a i)
                     (aref strings (read-u32 stream))))
      a)))

(defun read-type-list (stream types)
  (let* ((size (read-u32 stream))
         (l (make-array size)))
    (loop for i below size
          do (setf (aref l i)
                   (aref types (read-u16 stream))))
    l))

(defun read-prototypes (stream count start strings types)
  (when (plusp count)
    (file-position stream start)
    (let ((a (make-array count)))
      ;; read inline info
      (loop for i below count
            for short = (aref strings (read-u32 stream))
            for return-type = (aref types (read-u32 stream))
            for params-offset = (read-u32 stream)
            do (setf (aref a i)
                     (list short return-type params-offset)))
      ;; read parameter data
      (loop for prototype across a
            for off = (third prototype)
            do (setf (third prototype)
                     (when (plusp off)
                       (file-position stream off)
                       (read-type-list stream types))))
      a)))

(defun read-fields (stream count start strings types)
  (when (plusp count)
    (file-position stream start)
    (let ((a (make-array count)))
      ;; read inline info
      (loop for i below count
            do (setf (aref a i)
                     (list (aref types (read-u16 stream))
                           (aref types (read-u16 stream))
                           (aref strings (read-u32 stream))
                           ;; leave space to store instance later
                           nil)))
      a)))

(defun read-methods (stream count start
                     strings types prototypes)
  (when (plusp count)
    (file-position stream start)
    (let ((a (make-array count)))
      ;; read inline info
      (loop for i below count
            do (setf (aref a i)
                     (list (aref types (read-u16 stream))
                           (aref prototypes (read-u16 stream))
                           (aref strings (read-u32 stream))
                           ;; leave space to store instance later
                           nil)))
      a)))


(defun read-tries (stream count)
  (when (plusp count)
    (map-into (make-array count)
              (lambda ()
                (make-instance 'dex-try-block
                               :start (read-u32 stream)
                               :count (read-u16 stream)
                               :handlers (read-u16 stream))))))

(defun read-handler-list (stream types)
  ;; 'tries' data structure indexes by byte offset, so we return a
  ;; hash mapping from that to actual values rather than a straight
  ;; sequence
  (let* ((start (file-position stream))
         (count (read-uleb128 stream))
         (hash (make-hash-table)))
    (dotimes (i count)
      (let* ((pos (file-position stream))
             (size (read-sleb128 stream))
             (handlers (dotimes (j (abs size))
                         (list (aref types (read-uleb128 stream))
                               (read-uleb128 stream))))
             (catch-all (unless (plusp size)
                          (read-uleb128 stream))))
        (setf (gethash (- pos start) hash)
              (make-instance 'dex-catch-handler
                             :handlers handlers
                             :catch-all catch-all))))
    hash))

(defun read-debug-info (stream strings types)
  (let* ((start (read-uleb128 stream))
         (psize (read-uleb128 stream))
         (params (coerce
                  (loop repeat psize for i = (read-uleb128+1 stream)
                        collect (unless (minusp i) (aref strings i)))
                  'vector))
         (bytecode nil))
    ;; looks like we need to parse the bytecode to find the end reliably...
    (flet ((name ()
             (let ((a (read-uleb128+1 stream)))
               (unless (minusp a) (aref strings a))))
           (type ()
             (let ((a (read-uleb128+1 stream)))
               (unless (minusp a) (aref types a))))
           (u () (read-uleb128 stream))
           (s () (read-sleb128 stream)))
      (setf bytecode
            (loop for code = (read-u8 stream)
                  collect (case code
                            (0 (list :end-sequence))
                            (1 (list :advance-pc (u)))
                            (2 (list :advance-line (s)))
                            (3 (list :start-local (u) (name) (type)))
                            (4 (list :start-local-extended
                                     (u) (name) (type) (name)))
                            (5 (list :end-local (u)))
                            (6 (list :restart-local (u)))
                            (7 (list :prologue-end))
                            (8 (list :epilogue-begin))
                            (9 (list :set-file (name)))
                            ;; possibly should expand 'special' into
                            ;; line+pc offsets here rather than making user
                            ;; do it?
                            (t
                             (list :special code)))
                  while (/= code 0))))
    (make-instance 'dex-debug-info :start start :parameters params
                                   :bytecode bytecode)))

(defun read-code (method stream strings types)
  (setf (code method)
        (unless (zerop (code method))
          (file-position stream (code method))
          (let* ((registers (read-u16 stream))
                 (ins (read-u16 stream))
                 (outs (read-u16 stream))
                 (try-count (read-u16 stream))
                 (debug (read-u32 stream))
                 (count (read-u32 stream))
                 (instructions (read-ub16-vector count stream))
                 (padding (when (oddp count)
                            (read-u16 stream)))
                 (tries (read-tries stream try-count))
                 (handlers (when (plusp try-count)
                             (read-handler-list stream types))))
            (declare (ignore padding))
            (when tries
              (loop for i across tries
                    do (setf (handlers i)
                             (gethash (handlers i) handlers
                                      (list :missing-handler? (handlers i))))))
            (file-position stream debug)
            (make-instance 'dex-code
                           :registers registers
                           :ins ins
                           :outs outs
                           :debug-info (read-debug-info stream strings types)
                           :tries tries
                           :instructions (unassemble instructions))))))

(defun read-class-data (class stream strings types fields methods prototypes)
  (let ((static-fields (make-array (read-uleb128 stream)))
        (instance-fields (make-array (read-uleb128 stream)))
        (direct-methods (make-array (read-uleb128 stream)))
        (virtual-methods (make-array (read-uleb128 stream)))
        ;; fields/method indices are delta encoded, so store prev value here
        (prev-index 0))
    (flet ((read-field (type)
             (let* ((field-id (+ prev-index (read-uleb128 stream)))
                    (flags (read-uleb128 stream))
                    (field (aref fields field-id)))
               (setf prev-index field-id)
               ;; store the instance in the fields table, since other
               ;; things (annotations etc) reference them through that
               (setf (fourth field)
                     (make-instance type
                                    :name (third field)
                                    :type (second field)
                                    :flags (decode-flags flags *field-flags*)))))
           (read-method ()
             (let* ((method-id (+ prev-index (read-uleb128 stream)))
                    (flags (read-uleb128 stream))
                    (code (read-uleb128 stream))
                    (method (aref methods method-id)))
               (setf prev-index method-id)
               (setf (fourth method)
                     (make-instance 'dex-class-method
                                    :name (third method)
                                    :return-type (second (second method))
                                    :parameters (third (second method))
                                    :flags (decode-flags flags *method-flags*)
                                    :code code)))))
      ;; read the field and method definitions
      (setf prev-index 0)
      (dotimes (i (length static-fields))
        (setf (aref static-fields i) (read-field 'dex-class-static-field)))
      (setf prev-index 0)
      (dotimes (i (length instance-fields))
        (setf (aref instance-fields i) (read-field 'dex-class-field)))
      (setf prev-index 0)
      (dotimes (i (length direct-methods))
        (setf (aref direct-methods i) (read-method)))
      (setf prev-index 0)
      (dotimes (i (length virtual-methods))
        (setf (aref virtual-methods i) (read-method)))
      ;; read the code blocks for each method
      (map 'nil (lambda (a) (read-code a stream strings types)) direct-methods)
      (map 'nil (lambda (a) (read-code a stream strings types))
           virtual-methods))
    (setf (static-fields class) static-fields
          (instance-fields class) instance-fields
          (direct-methods class) direct-methods
          (virtual-methods class) virtual-methods))
  class)

(defun read-encoded-annotation (stream strings types fields methods)
  (let ((type (aref types (read-uleb128 stream)))
        (size (read-uleb128 stream))
        (a (make-hash-table :test 'equal)))
    (dotimes (i size)
      (setf (gethash (aref strings (read-uleb128 stream)) a)
            (read-encoded-value stream strings types fields methods)))
    ;; fixme: do something with this?
    (list :annotation :type type :annotations a)))

(defun read-encoded-value (stream strings types fields methods)
  (let* ((arg+type (read-u8 stream))
         (arg (ldb (byte 3 5) arg+type))
         (type (ldb (byte 5 0) arg+type)))
    (flet ((u32 ()
             (loop for i below (1+ arg)
                   sum (ash (read-u8 stream) (* i 8)))))
      ;; todo: rage check ARG
     (case type
       (#x00 ;; signed byte arg should be 0
        (read-s8 stream))
       (#x01 ;; signed short
        (let* ((lo (read-u8 stream))
               (hi (cond
                     ((plusp arg) (read-u8 stream))
                     ((logbitp 7 lo) -1)
                     (t 0))))
          (logior (ash hi 8) lo)))
       (#x02 ;; (unsigned 16-bit) shar
        (let ((lo (read-u8 stream))
              (hi (if (plusp arg) (read-u8 stream) 0)))
          (logior (ash hi 8) lo)))
       (#x03 ;; signed int
        (let ((a (loop for i below (1+ arg)
                       sum (ash (read-u8 stream) (* i 8)))))
          (when (and (/= arg 3) (logbitp (+ 7 (* arg 8)) a))
            (setf a (logior a (ash -1 (* 8 (1+ arg))))))
          a))
       (#x04 ;; signed long
        (let ((a (loop for i below (1+ arg)
                       sum (ash (read-u8 stream) (* i 8)))))
          (when (and (/= arg 7) (logbitp (+ 7 (* arg 8)) a))
            (setf a (logior a (ash -1 (* 8 (1+ arg))))))
          a))
       (#x10 ;; float32
        (ieee-floats:decode-float32
         (ash (loop for i below (1+ arg)
                    sum (ash (read-u8 stream) (* i 8)))
              (* 8 (- 3 arg)))))
       (#x11 ;; float64
        (ieee-floats:decode-float64
         (ash (loop for i below (1+ arg)
                    sum (ash (read-u8 stream) (* i 8)))
              (* 8 (- 7 arg)))))
       (#x17 ;; string
        (aref strings (u32)))
       (#x18 ;; type
        (aref types (u32)))
       (#x19 ;; field
        (aref fields (u32)))
       (#x1a ;; method
        (aref methods (u32)))
       (#x1b ;; enum
        (aref fields (u32)))
       (#x1c ;; array
        (read-encoded-array stream strings types fields methods ))
       (#x1d ;; annotation
        (read-encoded-annotation stream strings types fields methods ))
       (#x1e ;; null
        nil)
       (#x1f ;; boolean
        (not (zerop arg)))
       (t (error "invalid encoded_value? type = #x~2,'0x, arg = ~d" type arg))
       ))))

(defun read-encoded-array (stream strings types fields methods )
  (let ((size (read-uleb128 stream)))
    (map-into (make-array size)
              (lambda () (read-encoded-value
                          stream strings types fields methods)))))


(defun decode-visibility (x)
  (ecase x (0 :build) (1 :runtime) (2 :system)))

(defun read-annotation (stream strings types fields methods)
  ;; read an annotation_set_item
  (let* ((size (read-u32 stream))
         (offs (read-ub32-vector size stream)))
    (coerce
     (loop for off across offs
           do (file-position stream off)
           collect (apply 'make-instance 'dex-annotation
                          :visibility (decode-visibility (read-u8 stream))
                          (cdr
                           (read-encoded-annotation stream strings types
                                                    fields methods))))
     'vector)))

(defun read-annotations (class stream strings types fields methods )
  ;; decode annotations_directory_item and apply the annotations to
  ;; the parts of a dex-class instance
  (let* ((class-annotations (read-u32 stream))
         ;; read lists of id + offset from annotations_directory_item
         (fsize (read-u32 stream))
         (msize (read-u32 stream))
         (psize (read-u32 stream))
         (fa (loop for i below fsize
                   collect (list (read-u32 stream) (read-u32 stream))))
         (ma (loop for i below msize
                   collect (list (read-u32 stream) (read-u32 stream))))
         (pa (loop for i below psize
                   collect (list (read-u32 stream) (read-u32 stream)))))
    ;; class annotations
    (when (plusp class-annotations)
      (file-position stream class-annotations)
      (setf (annotations class) (read-annotation stream strings types
                                                 fields methods)))
    ;; find the actual annotations, and add to the specified fields,etc
    (loop for (id off) in fa
          for field = (fourth (aref fields id))
          do (unless (annotations field)
               (setf (annotations field) (make-array 0 :adjustable t
                                                       :fill-pointer 0)))
             (file-position stream off)
             (vector-push-extend
              (read-annotation stream strings types fields methods)
              (annotations field)))
    (loop for (id off) in ma
          for method = (fourth (aref methods id))
          do (unless (annotations method)
               (setf (annotations method) (make-array 0 :adjustable t
                                                        :fill-pointer 0)))
             (file-position stream off)
             (vector-push-extend
              (read-annotation stream strings types fields methods)
              (annotations method)))
    (loop for (id off) in pa
          for method = (fourth (aref methods id))
          do (unless (parameter-annotations method)
               (setf (parameter-annotations method)
                     (make-array (length (parameters method))
                                 :initial-element nil)))
             (file-position stream off)
             (let* ((s (read-u32 stream))
                    (pofs (read-ub32-vector s stream)))
               (loop for pid from 0
                     for poff across pofs
                     do  (unless (aref (parameter-annotations method) pid)
                           (setf (aref (parameter-annotations method) pid)
                                 (make-array 0 :adjustable t
                                               :fill-pointer 0)))
                         (file-position stream poff)
                         (vector-push-extend
                          (read-annotation stream strings types fields methods)
                          (aref (parameter-annotations method) pid)))))))

(defun read-classes (stream count start strings types fields methods prototypes)
  (when (plusp count)
    (file-position stream start)
    (let ((a (make-array count)))
      ;; read all of the class definitions
      (dotimes (i count)
        (setf (aref a i)
              (list (read-u32 stream) (read-u32 stream) (read-u32 stream)
                    (read-u32 stream) (read-u32 stream) (read-u32 stream)
                    (read-u32 stream) (read-u32 stream))))
      ;; find the individual components and build classes
      (dotimes (i count)
        (destructuring-bind (type flags super interfaces source-file
                             annotations class-data static-values)
            (aref a i)
          (let ((c (make-instance 'dex-class
                                  :type-name (aref types type)
                                  :flags (decode-flags flags *class-flags*)
                                  :superclass (unless (= super +no-index+)
                                                (aref types super))
                                  :source-file (unless (= source-file +no-index+)
                                                 (aref strings source-file)))))
            (when (plusp interfaces)
              (file-position stream interfaces)
              (setf (interfaces c) (read-type-list stream types)))
            (when (plusp class-data)
              (file-position stream class-data)
              (read-class-data c stream strings types fields methods prototypes))
            (when (plusp annotations)
              (file-position stream annotations)
              (read-annotations c stream strings types fields methods))
            (when (plusp static-values)
              (file-position stream static-values)
              (let ((v (read-encoded-array stream strings types fields methods )))
                (map 'nil (lambda (field value)
                            (setf (value field) value))
                     (static-fields c)
                     v)))
            (setf (aref a i) c)
)))
      a)))

(defun read-dex-file (stream)
  (let* ((magic (read-ub8-vector 8 stream))
         (version (check-dex-magic magic))
         (checksum (read-u32 stream))
         (signature (read-ub8-vector 20 stream))
         (file-size (read-u32 stream))
         (header-size (read-u32 stream))
         (endian-tag (read-u32 stream))
         (*read-endian* (cond
                          ((= endian-tag +dex-endian-constant+)
                           :le)
                          ((= endian-tag +dex-reverse-endian-constant+)
                           :be)
                          (t (error "got bad endian tag ~x?" endian-tag))))
         (link-size (read-u32 stream))
         (link-off (read-u32 stream))
         (map-off (read-u32 stream))
         (strings-size (read-u32 stream))
         (strings-off (read-u32 stream))
         (types-size (read-u32 stream))
         (types-off (read-u32 stream))
         (prototypes-size (read-u32 stream))
         (prototypes-off (read-u32 stream))
         (fields-size (read-u32 stream))
         (fields-off (read-u32 stream))
         (methods-size (read-u32 stream))
         (methods-off (read-u32 stream))
         (classes-size (read-u32 stream))
         (classes-off (read-u32 stream))
         (data-size (read-u32 stream))
         (data-off (read-u32 stream)))
    ;; possibly need to swap byte order of file-size, header-size if we
    ;; got a big-endian file?
    (when (and version
               (<= (+ data-size data-off) (file-length stream)))
      ;; todo: sanity check sizes, offsets, counts
      ;; todo: verify checksums/hashes?
      ;; todo: signal a restartable error if data is more than a few hundred MB?
      (file-position stream data-off)
      (let* (#++(data (read-ub8-vector data-size stream))
             ;; :map (read-map stream map-off)
             (link-table (read-link-table stream link-off link-size))
             (strings (read-strings stream strings-size strings-off))
             (types (read-types stream types-size types-off strings))
             (prototypes (read-prototypes stream
                                          prototypes-size prototypes-off
                                          strings types))
             (fields (read-fields stream fields-size fields-off
                                  strings types))
             (methods (read-methods stream methods-size methods-off
                                    strings types prototypes))
             (classes (read-classes stream classes-size classes-off
                                    strings types fields methods prototypes))
             #++(data (read-data stream data-size data-off))
             )
        (make-instance
         'dex-file
         :version version
         :endian *read-endian*
         :link-table link-table
         :strings strings
         :types types
         :prototypes prototypes
         :fields fields
         :methods methods
         :classes classes
         ))
    )))
