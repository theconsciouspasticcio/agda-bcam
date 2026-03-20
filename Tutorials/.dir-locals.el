;;; Presentation setup for the SetTheoryVsTypes tutorial.
;;; Emacs asks "apply dir-locals?" when opening a file here.  Say yes.
;;;
;;; This loads stt-present.el and activates the custom minor mode.
;;; See stt-present.el for the full keybinding list (F1–F12).

((agda2-mode
  . ((eval . (progn
               (load-file (expand-file-name "stt-present.el"
                            (file-name-directory
                              (or buffer-file-name default-directory))))
               (stt-present-mode 1))))))
