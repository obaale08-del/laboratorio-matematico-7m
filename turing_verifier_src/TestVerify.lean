import TuringVerifier.IntervalArithmetic

-- Probamos diferentes intervalos para ver cuál satisface i.verify
def int1 : ExactInterval := ExactInterval.mk 1 1 2 1 (by norm_num) (by norm_num) (by norm_num) -- [1, 2]
def int2 : ExactInterval := ExactInterval.mk (-1) 1 1 1 (by norm_num) (by norm_num) (by norm_num) -- [-1, 1]

#eval int1.verify
#eval int2.verify
