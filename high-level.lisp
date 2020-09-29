(in-package :sodium.high-level)


;; Tries to bridge the FFI canyon.
;; Input data can be 
;; - a UB8 vector, 
;; - a string, 
;; - a hex string via (:HEX "cafe"),
;; - another foreign pointer via (:FOREIGN ptr len)


(declaim (inline copy-to-foreign-fn))
(defun copy-to-foreign-fn (input initial-element string-padding? name)
  "Returns the number of bytes in INPUT, and a function that
  will at first return bytes from INPUT and then INITIAL-ELEMENT."
  (flet 
      ((copy-ub8 (input)
         (let ((p 0)
               (l (length input)))
           (values l
                   (lambda ()
                     (if (< p l)
                         (let ((v (aref input p)))
                           (unless (and (integerp v)
                                        (<= 0 v #xff))
                             (error "Invalid input byte at index ~d: ~d = #x~x" p v v))
                           (incf p)
                           v)
                         initial-element)))))
       (copy-stg (input)
         (let ((p 0)
               (l (length input)))
           (values (+ l (if string-padding? 1 0))
                   (lambda ()
                     (if (< p l)
                         (prog1
                             (char-code (aref input p))
                           (incf p))
                         initial-element))))))
    ;; TODO: allow bignums for priv/pub keys? Needs a :be/:le spec, and a size for messages
    ;; TODO: allow (:pub-key <pointer>), (:priv-key <pointer>), (:sec-key <pointer>)?
    ;; Make that a generic already?
    (cond
      ((null input)
       (values 0
               (lambda ()
                 initial-element)))
      ((stringp input)
       (copy-stg input))
      ((vectorp input)
       (copy-ub8 input))
      ((consp input)
       (ecase (first input)
         (:hex
          (destructuring-bind (hex) (rest input)
            (assert (stringp hex))
            (copy-ub8 (ironclad:hex-string-to-byte-array hex))))
         ;; (:foreign <pointer> <len>) to pass data directly on
         (:foreign
          (destructuring-bind (ptr len) (rest input)
            (assert (typep ptr 'cffi:foreign-pointer))
            (assert (integerp len))
            (values len ptr)))))
      (T
       (error "bad type for ~s, got ~s" name input)))))


(defmacro with-foreign-bytes ((name source &key len start initial-element 
                                    req-input-len string-padding?
                                    (len-sym (gensym "LEN")))
                              &body body)
  "Allocates foreign space with LEN bytes, and copies SOURCE
  starting at position START in there,
  padding with INITIAL-ELEMENT, if necessary.
  The buffer length can alternatively be calculated as (+ START <bytes in SOURCE>).
  After BODY the foreign buffer is cleared."
  (check-type name symbol)
  (alexandria:once-only (source len initial-element start req-input-len string-padding?)
    (alexandria:with-gensyms (i fn val input-len start% len% thunk)
      `(multiple-value-bind (,input-len ,fn)
           (copy-to-foreign-fn ,source (or ,initial-element 0) ,string-padding?)
         (when (and ,req-input-len
                    (/= ,input-len ,req-input-len))
           (error "Bad input length ~d for ~s, ~d bytes are required"
                  ,input-len ',name ,req-input-len))
         (flet ((,thunk (,name ,len-sym)
                  (declare (ignorable ,len-sym))
                  ,@ body))
           (let* ((,i 0)
                  (,start% (or ,start 0))
                  ;; internal symbol
                  (,len% (or ,len
                             (+ ,start% ,input-len))))
             (cond
               ((typep ,fn 'cffi:foreign-pointer)
                ;; Already a foreign pointer, no need to copy data around.
                ;; TODO: use unwind-protect all the same??
                (,thunk ,fn ,len%))
               (t
                (cffi:with-foreign-object (,name 
                                            `(:array :uchar ,,len%))
                  (loop while (< ,i ,start%)
                        do (setf (cffi:mem-aref ,name :uchar ,i)
                                 ,initial-element)
                        do (incf ,i))
                  (loop while (< ,i ,len%)
                        for ,val = (funcall ,fn)
                        do (setf (cffi:mem-aref ,name :uchar ,i)
                                 ,val)
                        do (incf ,i))
                  #-(or)
                  (format *trace-output* "~s: ~a~&" ',name
                          (foreign-memory-as-hex-string ,name ,len%))
                  (unwind-protect
                      (,thunk ,name ,len%)
                    ;; Use the internal length, in case the user-visible one was changed.
                    (sodium::sodium-memzero ,name ,len%)))))))))))


(defun foreign-memory-as-string (address &optional len)
  "Pure dump function."
  (cffi:foreign-string-to-lisp address :count len))

(defun foreign-memory-as-hex-string (address len)
  "Pure dump function."
  (ironclad:byte-array-to-hex-string 
    (cffi:foreign-array-to-lisp address
                                `(:array :uchar , len)
                                :element-type '(unsigned-byte 8))))

(defun foreign-memory-as-b64-string (address len)
  "Pure dump function."
  (base64:string-to-base64-string 
    (cffi:foreign-array-to-lisp address
                                `(:array :uchar , len)
                                :element-type '(unsigned-byte 8))))




(defun symmetrically-encrypt (message key nonce fn)
  "Runs FN with the encrypted message, its length, the nonce, and its length,
  as foreign pointers resp. numbers.
  If NONCE is NIL, it gets randomly generated.
  The foreign pointers become invalid when FN returns."
  (with-foreign-bytes (f-msg message 
                             :len-sym msg-len
                             :string-padding? nil)
    (with-foreign-bytes (f-key key :req-input-len (sodium:crypto-secretbox-keybytes))
      (with-foreign-bytes (f-nonce nonce :len (sodium:crypto-secretbox-noncebytes))
        (when (not nonce)
          (sodium:randombytes-buf f-nonce (sodium:crypto-secretbox-noncebytes)))
        (let ((enc-len (+ msg-len (sodium:crypto-secretbox-macbytes))))
          (with-foreign-bytes (f-enc nil :len enc-len)
            (let ((result (sodium:crypto-secretbox-easy f-enc
                                                        f-msg msg-len
                                                        f-nonce
                                                        f-key)))
              (if (zerop result)
                  (funcall fn 
                           f-enc enc-len
                           f-nonce (sodium:crypto-secretbox-noncebytes))
                  (error "Can't encrypt")))))))))


(defun symmetrically-decrypt (enc key nonce fn)
  "Runs FN with the decrypted message as foreign pointer and its length.
  The foreign pointer becomes invalid when FN returns."
  (with-foreign-bytes (f-enc enc :len-sym enc-len)
    (with-foreign-bytes (f-key key :req-input-len (sodium:crypto-secretbox-keybytes))
      (with-foreign-bytes (f-nonce nonce :req-input-len (sodium:crypto-secretbox-noncebytes))
        (let ((msg-len (- enc-len (sodium:crypto-secretbox-macbytes))))
          (let ((result (sodium:crypto-secretbox-open-easy f-enc
                                                           f-enc enc-len
                                                           f-nonce
                                                           f-key)))
            (if (zerop result)
                (funcall fn 
                         f-enc msg-len)
                (error "Can't decrypt"))))))))


(defun priv-pubkey-encrypt (message privkey pubkey nonce fn)
  "Runs FN with the encrypted message and its length, the nonce, and its length,
  as foreign pointers resp. numbers.
  If NONCE is NIL, it gets randomly generated.
  The foreign pointers become invalid when FN returns."
  (with-foreign-bytes (f-msg message 
                             :len-sym msg-len
                             :string-padding? nil)
    (with-foreign-bytes (f-pub pubkey :req-input-len (sodium:crypto-box-publickeybytes))
      (with-foreign-bytes (f-nonce nonce :len (sodium:crypto-secretbox-noncebytes))
        (when (not nonce)
          (sodium:randombytes-buf f-nonce (sodium:crypto-box-noncebytes)))
        (with-foreign-bytes (f-priv privkey :req-input-len (sodium:crypto-box-secretkeybytes))
          (let ((enc-len (+ msg-len (sodium:crypto-box-macbytes))))
            (with-foreign-bytes (f-enc nil :len enc-len)
              (let ((result (sodium:crypto-box-easy f-enc
                                                    f-msg msg-len
                                                    f-nonce
                                                    f-pub f-priv
                                                    )))
                (if (zerop result)
                    (funcall fn 
                             f-enc enc-len
                             f-nonce (sodium:crypto-box-noncebytes))
                    (error "Can't encrypt"))))))))))


(defun priv-pubkey-decrypt (enc privkey pubkey nonce fn)
  "Runs FN with the decrypted message and its length,
  as foreign pointer resp. number.
  The foreign pointers become invalid when FN returns."
  (with-foreign-bytes (f-enc enc 
                             :len-sym enc-len
                             :string-padding? nil)
    (with-foreign-bytes (f-pub pubkey :req-input-len (sodium:crypto-box-publickeybytes))
      (with-foreign-bytes (f-nonce nonce :req-input-len (sodium:crypto-secretbox-noncebytes))
        (with-foreign-bytes (f-priv privkey :req-input-len (sodium:crypto-box-secretkeybytes))
          (let ((msg-len (- enc-len (sodium:crypto-box-macbytes))))
            (let ((result (sodium:crypto-box-open-easy f-enc 
                                                       f-enc enc-len
                                                       f-nonce
                                                       f-pub f-priv)))
              (if (zerop result)
                  (funcall fn 
                           f-enc msg-len)
                  (error "Can't decrypt")))))))))


(defun with-new-asymm-keypair% (fn)
  "Generate a new random keypair, and run FN with 
  the private part (as foreign pointer), its length, and
  the public part (as foreign pointer), and its length."
  (with-foreign-bytes (pub nil :len (sodium:crypto-box-publickeybytes))
    (with-foreign-bytes (sec nil :len (sodium:crypto-box-secretkeybytes))
      (sodium:crypto-box-keypair pub sec)
      (funcall fn 
               sec (sodium:crypto-box-secretkeybytes)
               pub (sodium:crypto-box-publickeybytes)))))


(defun with-new-symmetric-key% (fn)
  "Generate a new random key, and run FN with 
  the key (as foreign pointer), and its length."
  (with-foreign-bytes (sec nil :len (sodium:crypto-secretbox-keybytes))
    (sodium:crypto-secretbox-keygen sec)
    (funcall fn 
             sec (sodium:crypto-box-secretkeybytes))))

(defmacro with-new-symmetric-key ((key-sym &optional (key-len-sym (gensym "L"))) 
                              &body body)
  `(with-new-symmetric-key% 
     (lambda (,key-sym ,key-len-sym)
       (declare (ignorable ,key-len-sym))
       ,@ body)))

(defmacro with-new-asymmetric-keypair ((priv-key-sym pub-key-sym &optional pr-len-sym pb-len-sym)
                                   &body body)
  (check-type priv-key-sym symbol)
  (check-type pub-key-sym symbol)
  (if pr-len-sym
      (check-type pr-len-sym symbol)
      (setf pr-len-sym (gensym)))
  (if pb-len-sym
      (check-type pb-len-sym symbol)
      (setf pb-len-sym (gensym)))
  `(with-new-asymm-keypair% 
     (lambda (,priv-key-sym ,pr-len-sym ,pub-key-sym ,pb-len-sym)
       (declare (ignorable ,pb-len-sym ,pr-len-sym))
       ,@ body)))


(export '(with-new-asymmetric-keypair   
           with-new-symmetric-key
           priv-pubkey-encrypt
           priv-pubkey-decrypt
           symmetrically-encrypt
           symmetrically-decrypt
           foreign-memory-as-hex-string
           foreign-memory-as-b64-string
           foreign-memory-as-string))



#+(or)
(setf fiveam:*on-error* :debug
      fiveam:*run-test-when-defined* t)

(fiveam:def-test basic-conversions ()
  (fiveam:is (string= "cccc614230cccccc"
                      (with-foreign-bytes (x "aB0" :len 8 :start 2 :initial-element #xcc)
                        (foreign-memory-as-hex-string x 8))))
  (fiveam:is (string= "080706cc"
                      (with-foreign-bytes (x (vector 8 7 6) :len 4 :initial-element #xcc)
                        (foreign-memory-as-hex-string x 4))))
  (fiveam:is (string= "cccccccc01234567"
                      (with-foreign-bytes (x '(:hex "0123456789abcdef")
                                             :len-sym my-len
                                             :len 8 
                                             :start 4 
                                             :initial-element #xcc)
                        (foreign-memory-as-hex-string x 8)))))


(fiveam:def-test symmetric-enc-dec ()
  (let ((key '(:hex "0301010101010101010201010101010101010101010101010101010101010101"))
        (msg "Here I am"))
    (fiveam:is (equal (list msg (length msg))
                      (multiple-value-list
                        (symmetrically-encrypt
                          msg
                          key 
                          '(:hex "aa")
                          (lambda (enc enc-len nonce nonce-len)
                            (symmetrically-decrypt
                              (list :hex
                                    (foreign-memory-as-hex-string enc enc-len))
                              key
                              (list :hex
                                    (foreign-memory-as-hex-string nonce nonce-len))
                              (lambda (msg msg-len)
                                (foreign-memory-as-string msg msg-len))))))))))


(fiveam:def-test asymm-enc-dec ()
  (let ((pub '(:hex "0301010101010101010201010101010101010101010101010101010101010108"))
        (priv '(:hex "0401010201010101010201010101010101010101010101010101010101010109"))
        (msg "Here I am"))
    (fiveam:is (equal (list msg (length msg))
                      (multiple-value-list
                        (priv-pubkey-encrypt
                          msg
                          priv pub
                          #(128 #x40 33)
                          (lambda (enc enc-len nonce nonce-len)
                            (priv-pubkey-decrypt
                              (list :hex
                                    (foreign-memory-as-hex-string enc enc-len))
                              priv 
                              pub
                              (list :hex
                                    (foreign-memory-as-hex-string nonce nonce-len))
                              (lambda (msg msg-len)
                                (foreign-memory-as-string msg msg-len))))))))))

#+(or)
(fiveam:run-all-tests)
