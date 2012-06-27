(in-package #:3b-dex)

;; writer will refuse to write any format not in this list
(defparameter *supported-formats* '(35))
;; default version number to use in header
(defparameter *default-format* 35)

(defconstant +dex-endian-constant+ #x12345678)
(defconstant +dex-reverse-endian-constant+ #x78563412)

(defun ub8-vector (&key length contents (initial-element 0))
  (cond
    ((and length contents)
     (make-array length :element-type '(unsigned-byte 8)
                        :initial-contents contents))
    (length (make-array length :element-type '(unsigned-byte 8)
                               :initial-element initial-element))
    (contents (make-array (length contents) :element-type '(unsigned-byte 8)
                          :initial-contents contents))
    (t (error "must specify length or contents to UB8-VECTOR"))))

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

;;; readers assume (unsigned-byte 8) stream
;;; TODO: verify type of stream

(defun read-u8 (stream)
  (read-byte stream))

(defun read-s8 (stream)
  (let ((b (read-byte stream)))
    (if (< b 128)
        b
        (dpb b (byte 7 0) -1))))

#++
(flex:with-input-from-sequence (s #(0 1 127 128 255))
  (loop for a = (ignore-errors (read-s8 s)) while a collect a))

(defparameter *read-endian* :le)

(defun read-u16 (stream)
  (if (eq *read-endian* :le)
      (dpb (read-byte stream) (byte 8 0) (ash (read-byte stream) 8))
      (dpb (read-byte stream) (byte 8 8) (read-byte stream))))

(defun read-s16 (stream)
  (let ((b (read-u16 stream)))
    (if (< b 32768)
        b
        (dpb b (byte 15 0) -1))))

#++
(flex:with-input-from-sequence (s #(0 1 127 128 255 254))
  (loop for a = (ignore-errors (read-s16 s)) while a collect a))


(defun read-u32 (stream)
  (if (eq *read-endian* :le)
      (logior (read-byte stream) (ash (read-byte stream) 8)
              (ash (read-byte stream) 16) (ash (read-byte stream) 24))
      (logior (ash (read-byte stream) 24) (ash (read-byte stream) 16)
              (ash (read-byte stream) 8) (read-byte stream))))

(defun read-s32 (stream)
  (let ((b (read-u32 stream)))
    (if (< b #.(expt 2 31))
        b
        (dpb b (byte 31 0) -1))))

#++
(flex:with-input-from-sequence (s #(0 1 127 127 254 255 255 255))
  (loop for a = (ignore-errors (read-s32 s)) while a collect a))

(defun read-u64 (stream)
  (if (eq *read-endian* :le)
      (logior (read-byte stream) (ash (read-byte stream) 8)
              (ash (read-byte stream) 16) (ash (read-byte stream) 24)
              (ash (read-byte stream) 32) (ash (read-byte stream) 40)
              (ash (read-byte stream) 48) (ash (read-byte stream) 56))
      (logior (ash (read-byte stream) 56) (ash (read-byte stream) 48)
              (ash (read-byte stream) 40) (ash (read-byte stream) 32)
              (ash (read-byte stream) 24) (ash (read-byte stream) 16)
              (ash (read-byte stream) 8) (read-byte stream))))

(defun read-s64 (stream)
  (let ((b (read-u64 stream)))
    (if (< b #.(expt 2 63))
        b
        (dpb b (byte 63 0) -1))))

#++
(flex:with-input-from-sequence (s #(0 1 127 127 254 255 255 255))
  (loop for a = (ignore-errors (read-s64 s)) while a collect a))


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





(defun read-ub8-vector (length stream)
  (let ((v (ub8-vector :length length)))
    (read-sequence v stream)
    v))

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

(defun read-zero-terminated (stream min-size)
  (let ((buf (make-array (max min-size 1) :element-type '(unsigned-byte 8)
                                  :fill-pointer min-size
                                  :adjustable t)))
    (read-sequence buf stream)
    (when (find 0 buf)
      (error "got unexpected 0 in mutf8 encoded string?"))
    (loop for b = (read-byte stream)
          while (plusp b)
          do (vector-push-extend b buf))
    buf))



(defclass dex-file ()
  ((version :initform *default-format* :initarg :version :accessor version)
   (endian :initform :le :initarg :endian :accessor endian)
   (link-table :initarg :link-table :accessor link-table)
   (maps :initarg :maps :accessor map-list)
   (strings :initarg :strings :accessor strings)
   (types :initarg :types :accessor types)
   (prototypes :initarg :prototypes :accessor prototypes)
   (fields :initarg :fields :accessor fields)
   (methods :initarg :methods :accessor methods)
   (classes :initarg :classes :accessor classes)
   (data :initarg :data :accessor data)))



(defun read-link-table (stream count start data)
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
                           (aref strings (read-u32 stream)))))
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
                           (aref strings (read-u32 stream)))))
      a)))

(defun read-classes (stream count start)
  (when (plusp count)
    (let ((a (make-array count)))
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
             (classes (read-classes stream classes-size classes-off))
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
