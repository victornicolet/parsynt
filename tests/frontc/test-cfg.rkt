#lang racket

(require c "../../consynth/frontc/cfg.rkt"
         "../../consynth/frontc/pprint.rkt")

(define program (parse-program (open-input-file "test_cfg_all_constructs.c")))

(print-cfg (car (compute-cfg program)))

