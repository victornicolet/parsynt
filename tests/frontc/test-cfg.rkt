#lang racket

(require c consynth/frontc/cfg)

(define program (parse-program (open-input-file "test_cfg_all_constructs.c")))
(print-cfg (car (compute-cfg program)))

