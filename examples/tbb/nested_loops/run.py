from subprocess import call

experiments = [ 'Exp2DSorted',
                'Exp2DSum',
                'Exp2DSorted',
                'ExpGradient1',
                'ExpGradient2',
                'ExpMinMax',
                'ExpMaxDist',
                'ExpMinMaxCol',
                'ExpMaxLeftRect',
                'ExpMaxTopStrip',
                'ExpMaxBottomStrip',
                'ExpMaxSegStrip',
                'ExpMaxTopBox',
                'ExpMaxBottomBox',
                'ExpMaxSegBox',
                'ExpMTLR',
                'ExpMTRR',
                'ExpSaddlePoint',
                'ExpMode',
                'ExpOverlapping']

num_cores = [1, 2, 3, 4, 6, 8, 10, 12, 16, 20, 24, 32]


for nc in num_cores:
    for expr in experiments:
        call(["./" + expr, str(nc), ">> explog.csv"])