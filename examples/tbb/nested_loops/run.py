from subprocess import call

experiments = [ # 'Exp2DSorted',  
    # 'Exp2DSum',
    # 'ExpGradient1',
    # 'ExpGradient2',
    # 'ExpMinMax',
    # 'ExpMaxDist',
    # 'ExpMinMaxCol',
    # 'ExpMaxLeftRect',
    # 'ExpMaxTopStrip',
    # 'ExpMaxBottomStrip',
    # 'ExpMaxSegStrip',
    # 'ExpMaxTopBox',
    # 'ExpMaxBottomBox',
    # 'ExpMaxSegBox',
    'ExpMTLR',
    'ExpMTRR',
    'ExpSaddlePoint',
    'ExpMode',
    'ExpOverlapping']

num_cores = [1, 2, 3, 4, 6, 8, 10, 12, 16, 24, 32, 46, 58, 64]


for expr in experiments:
    for nc in num_cores:
        with open('explog_compsbk2.csv', 'a+') as myoutfile:
            call(["./" + expr, str(nc)], stdout=myoutfile)
