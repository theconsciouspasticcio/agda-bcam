;;; stt-present.el --- Presentation mode for "Set Theory vs Types" -*- lexical-binding: t; -*-

;; Custom Emacs minor mode for the SetTheoryVsTypes live tutorial.
;;
;; Load:  M-x load-file RET Tutorials/stt-present.el RET
;; Start: M-x stt-present-mode
;;
;; Or let .dir-locals.el do it automatically when you open the file.

;;; ---------- Demo script: pre-loaded normalize expressions ----------

;; F1 cycles through these, pre-filling the C-c C-n prompt.
;; The audience sees the expression, you press Enter, the result appears.

(defvar stt-demo-expressions
  '(;; §1 — types as constructors
    ("zero"                         "→ zero  (the constructor, not a numeral)")
    ("suc (suc (suc zero))"         "→ 3     (BUILTIN kicks in)")
    ;; §2 — propositions are types
    ("tt"                           "→ tt    (the unique proof of ⊤)")
    ;; §3 — computation on predicates (THE star demo)
    ("Even 0"                       "→ ⊤     (0 is even: trivially true)")
    ("Even 1"                       "→ ⊥     (1 is even: impossible)")
    ("Even 2"                       "→ ⊤")
    ("Even 3"                       "→ ⊥")
    ("Even 4"                       "→ ⊤")
    ("Even 100"                     "→ ⊤     (the machine just… does it)")
    ("Even 101"                     "→ ⊥")
    ;; §4 — definitional equality: computation has a direction
    ("2 + 2"                        "→ 4     (definitional: computes)")
    ("2 + 3"                        "→ 5")
    ("0 + 10"                       "→ 10    (first clause fires)")
    ;; these would need a variable, so they don't normalize further:
    ;; ("n + 0"                     "→ stuck! this is why +-idʳ needs induction")
    )
  "Demo expressions with presenter notes.  Car = expr, cadr = note.")

(defvar stt-demo-index 0
  "Current index in `stt-demo-expressions'.")

(defun stt-demo-next ()
  "Normalize the next expression in the demo script.
Pre-fills the C-c C-n prompt so the audience sees the expression.
Press Enter to compute.  Press C-g to skip."
  (interactive)
  (if (>= stt-demo-index (length stt-demo-expressions))
      (progn
        (setq stt-demo-index 0)
        (message "✓ Demo script complete.  F1 to restart from the top."))
    (let* ((entry (nth stt-demo-index stt-demo-expressions))
           (expr (car entry))
           (note (cadr entry)))
      (setq stt-demo-index (1+ stt-demo-index))
      (message "Demo %d/%d: %s   %s"
               stt-demo-index (length stt-demo-expressions) expr note)
      (minibuffer-with-setup-hook
          (lambda () (insert expr))
        (call-interactively #'agda2-compute-normalised-maybe-toplevel)))))

(defun stt-demo-reset ()
  "Reset the demo script to the beginning."
  (interactive)
  (setq stt-demo-index 0)
  (message "Demo script reset.  F1 to start."))

(defun stt-demo-prev ()
  "Go back one step in the demo script."
  (interactive)
  (setq stt-demo-index (max 0 (- stt-demo-index 2)))
  (stt-demo-next))


;;; ---------- Section navigation ----------

;; F3/F4 jump between §-marked sections.  Useful during Q&A or to skip ahead.

(defun stt-next-section ()
  "Jump to the next § section heading."
  (interactive)
  (let ((found nil))
    (save-excursion
      (forward-line 1)
      (when (re-search-forward "^-- §\\|^-- APPENDIX\\|^-- RESOURCES\\|^-- PRESENTER" nil t)
        (setq found (line-beginning-position))))
    (if found
        (progn (goto-char found) (recenter 2))
      (message "No more sections."))))

(defun stt-prev-section ()
  "Jump to the previous § section heading."
  (interactive)
  (let ((found nil))
    (save-excursion
      (beginning-of-line)
      (when (re-search-backward "^-- §\\|^-- APPENDIX\\|^-- RESOURCES\\|^-- PRESENTER" nil t)
        (setq found (line-beginning-position))))
    (if found
        (progn (goto-char found) (recenter 2))
      (message "Already at the top."))))


;;; ---------- 30-minute timer ----------

;; Mode-line shows elapsed time and a countdown.

(defvar stt--start-time nil "When the presentation started.")
(defvar stt--timer-object nil "The repeating timer for mode-line updates.")
(defvar stt--timer-string "" "Current timer string for the mode line.")

(defun stt--update-timer ()
  "Update the mode-line timer string."
  (when stt--start-time
    (let* ((elapsed (floor (float-time (time-subtract (current-time) stt--start-time))))
           (minutes (/ elapsed 60))
           (seconds (% elapsed 60))
           (remaining (max 0 (- 30 minutes))))
      (setq stt--timer-string
            (propertize (format " [%02d:%02d | %dmin left]" minutes seconds remaining)
                        'face (if (<= remaining 5) 'error 'success)))
      (force-mode-line-update t))))

(defun stt-timer-start ()
  "Start the 30-minute presentation timer."
  (interactive)
  (setq stt--start-time (current-time))
  (when stt--timer-object (cancel-timer stt--timer-object))
  (setq stt--timer-object (run-with-timer 0 1 #'stt--update-timer))
  (message "Timer started.  30 minutes on the clock."))

(defun stt-timer-stop ()
  "Stop the timer."
  (interactive)
  (when stt--timer-object
    (cancel-timer stt--timer-object)
    (setq stt--timer-object nil))
  (setq stt--timer-string "")
  (force-mode-line-update t)
  (message "Timer stopped."))


;;; ---------- Chalkboard: quick-reference popup ----------

;; F10 flashes the Curry-Howard table in a temporary buffer.
;; Press q to dismiss.

(defvar stt-chalkboard-text
  "
  ╔══════════════════════════════════════════════════════════════════╗
  ║           CURRY-HOWARD CORRESPONDENCE — CHEAT SHEET            ║
  ╠══════════════════╦══════════════════════╦══════════════════════╣
  ║  Logic           ║  Type theory (Agda)  ║  You know this as    ║
  ╠══════════════════╬══════════════════════╬══════════════════════╣
  ║  ⊥  (false)      ║  ⊥  (empty type)     ║  ∅                   ║
  ║  ⊤  (true)       ║  ⊤  (unit type)      ║  {∗}                 ║
  ║  P ∧ Q           ║  P × Q              ║  cartesian product   ║
  ║  P ∨ Q           ║  P ⊎ Q              ║  disjoint union      ║
  ║  P ⟹ Q          ║  P → Q              ║  Hom(P,Q)            ║
  ║  ¬ P             ║  P → ⊥              ║  complement          ║
  ║  ∀x∈A. P(x)     ║  (x : A) → P x      ║  sections of bundle  ║
  ║  ∃x∈A. P(x)     ║  Σ A P              ║  total space         ║
  ╠══════════════════╬══════════════════════╬══════════════════════╣
  ║  proposition     ║  type                ║                      ║
  ║  proof           ║  term (= program)    ║                      ║
  ║  true / false    ║  inhabited / empty   ║                      ║
  ╠══════════════════╩══════════════════════╩══════════════════════╣
  ║  x ∈ A = proposition (can be true or false)                    ║
  ║  x : A = judgment    (static, unchallengeable)                 ║
  ║                                                                ║
  ║  Definitional equality: the machine checks by computation.     ║
  ║  Propositional equality: you prove it (≡ with refl).           ║
  ║  0 + n = n  is free.   n + 0 = n  costs an induction proof.   ║
  ╚════════════════════════════════════════════════════════════════╝

                         [press q to close]
"
  "The chalkboard reference card.")

(defun stt-chalkboard ()
  "Pop up the Curry-Howard cheat sheet."
  (interactive)
  (let ((buf (get-buffer-create "*STT Chalkboard*")))
    (with-current-buffer buf
      (let ((inhibit-read-only t))
        (erase-buffer)
        (insert stt-chalkboard-text)
        (goto-char (point-min))
        (special-mode)
        (setq-local face-remapping-alist
                    '((default :height 1.4 :family "Monospace")))))
    (pop-to-buffer buf '((display-buffer-at-bottom)
                         (window-height . fit-window-to-buffer)))))


;;; ---------- The minor mode ----------

(defvar stt-present-mode-map
  (let ((map (make-sparse-keymap)))
    ;; Demo script
    (define-key map (kbd "<f1>")  #'stt-demo-next)
    (define-key map (kbd "S-<f1>") #'stt-demo-prev)
    (define-key map (kbd "<f2>")  #'stt-demo-reset)
    ;; Section navigation
    (define-key map (kbd "<f3>")  #'stt-prev-section)
    (define-key map (kbd "<f4>")  #'stt-next-section)
    ;; Standard Agda actions (one key instead of C-c C-x)
    (define-key map (kbd "<f5>")  #'agda2-compute-normalised-maybe-toplevel)
    (define-key map (kbd "<f6>")  #'agda2-goal-and-context)
    (define-key map (kbd "<f7>")  #'agda2-make-case)
    (define-key map (kbd "<f8>")  #'agda2-auto-maybe-all)
    (define-key map (kbd "<f9>")  #'agda2-refine)
    ;; Chalkboard & timer
    (define-key map (kbd "<f10>") #'stt-chalkboard)
    (define-key map (kbd "<f11>") #'stt-timer-start)
    (define-key map (kbd "<f12>") #'agda2-load)
    map)
  "Keymap for `stt-present-mode'.")

;;;###autoload
(define-minor-mode stt-present-mode
  "Presentation mode for the SetTheoryVsTypes tutorial.

Binds F1–F12 to presentation actions:

  F1          Next demo expression (pre-fills normalize prompt)
  Shift-F1    Previous demo expression
  F2          Reset demo script
  F3 / F4     Previous / next § section
  F5          Normalize (manual, type your own expression)
  F6          Show goal & context
  F7          Case split
  F8          Auto-solve
  F9          Refine
  F10         Chalkboard (Curry-Howard reference card)
  F11         Start 30-minute timer
  F12         Load file (typecheck)"
  :lighter " STT"
  :keymap stt-present-mode-map
  (if stt-present-mode
      (progn
        ;; Big font for projection
        (text-scale-set 3)
        ;; Timer in mode line
        (unless (member '(:eval stt--timer-string) mode-line-misc-info)
          (push '(:eval stt--timer-string) mode-line-misc-info))
        (stt-timer-start)
        (message "STT presentation mode ON.  F1=demo  F3/F4=sections  F10=chalkboard  F11=timer"))
    ;; Cleanup
    (text-scale-set 0)
    (stt-timer-stop)
    (setq mode-line-misc-info
          (delete '(:eval stt--timer-string) mode-line-misc-info))
    (message "STT presentation mode OFF.")))

(provide 'stt-present)
;;; stt-present.el ends here
