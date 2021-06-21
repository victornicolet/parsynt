cmake_minimum_required(VERSION 3.5)
project(DivideExperiments)

link_libraries(tbb)

set(CMAKE_BUILD_DIRECTORY build)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11 -ltbb -fopenmp")
set(CMAKE_SOURCE_DIR src)
set(SOURCE_FILES src/param.h src/StopWatch.h src/StopWatch.cpp src/datagen.cpp src/datagen.h)

# All experiment executables start with prefix Exp
# CINS
add_executable(PtExpCins src/pt_cins.cpp ${SOURCE_FILES})
# CLO
add_executable(PtExpClo src/pt_clo.cpp ${SOURCE_FILES})
# HIS
add_executable(PtExpHis src/pt_his.cpp ${SOURCE_FILES})
# KSMALL
add_executable(PtExpKSmall src/pt_ksm.cpp ${SOURCE_FILES})
# KLARGEST
add_executable(PtExpKla src/pt_kla.cpp ${SOURCE_FILES})
# MIP
add_executable(PtExpMip src/pt_mip.cpp ${SOURCE_FILES})
target_link_libraries(PtExpMip ${OpenCV_LIBS})
# POP
add_executable(PtExpPop src/pt_pop.cpp  ${SOURCE_FILES})
target_link_libraries(PtExpPop ${OpenCV_LIBS})
# PEP
add_executable(PtExpPep src/pt_pep.cpp  ${SOURCE_FILES})
target_link_libraries(PtExpPep ${OpenCV_LIBS})
# QOC
add_executable(PtExpQoc src/pt_qoc.cpp ${SOURCE_FILES})
target_link_libraries(PtExpQoc ${OpenCV_LIBS})
# SOR
add_executable(PtExpSor src/pt_sor.cpp ${SOURCE_FILES})
# INS
add_executable(PtExpIns src/pt_ins.cpp ${SOURCE_FILES})

# Prefix divides vs. conditional auxiliary (13 benchmarks)
# COTT
add_executable(PdExpCott src/pd_cott.cpp ${SOURCE_FILES})
# COZP
add_executable(PdExpCozp src/pd_cozp.cpp ${SOURCE_FILES})
# COZST
add_executable(PdExpCozst src/pd_cozst.cpp ${SOURCE_FILES})
# COZSTZST
add_executable(PdExpCozstzst src/pd_cozstzst.cpp ${SOURCE_FILES})
# LIS
add_executable(PdExpLis src/pd_lis.cpp ${SOURCE_FILES})
# LMO
add_executable(PdExpLmo src/pd_lmo.cpp ${SOURCE_FILES})
# MBO
add_executable(PdExpMbo src/pd_mbo.cpp ${SOURCE_FILES})
# MLBO
add_executable(PdExpMlbo src/pd_mlbo.cpp ${SOURCE_FILES})
# MBOZST
add_executable(PdExpMbozst src/pd_mbozst.cpp ${SOURCE_FILES})
# MDO
add_executable(PdExpMdo src/pd_mdo.cpp ${SOURCE_FILES})
# MLEZ
add_executable(PdExpMlez src/pd_mlez.cpp ${SOURCE_FILES})
# MLOZOS
add_executable(PdExpMlozos src/pd_mlozos.cpp ${SOURCE_FILES})
# MSZ
add_executable(PdExpMsz src/pd_msz.cpp ${SOURCE_FILES})