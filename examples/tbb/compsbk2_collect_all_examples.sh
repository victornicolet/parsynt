#!/bin/sh
echo "Starting collections ..."
. ~/intel/vtune_amplifier_xe/bin64/amplxe-cl  -collect general-exploration -- ./tbb_test -s30 -n64 -e sum
. ~/intel/vtune_amplifier_xe/bin64/amplxe-cl  -collect general-exploration -- ./tbb_test -s30 -n64 -e min
. ~/intel/vtune_amplifier_xe/bin64/amplxe-cl  -collect general-exploration -- ./tbb_test -s30 -n64 -e max
. ~/intel/vtune_amplifier_xe/bin64/amplxe-cl  -collect general-exploration -- ./tbb_test -s30 -n64 -e mi2
. ~/intel/vtune_amplifier_xe/bin64/amplxe-cl  -collect general-exploration -- ./tbb_test -s30 -n64 -e col
. ~/intel/vtune_amplifier_xe/bin64/amplxe-cl  -collect general-exploration -- ./tbb_test -s30 -n64 -e len
. ~/intel/vtune_amplifier_xe/bin64/amplxe-cl  -collect general-exploration -- ./tbb_test -s30 -n64 -e pop
. ~/intel/vtune_amplifier_xe/bin64/amplxe-cl  -collect general-exploration -- ./tbb_test -s30 -n64 -e pot
. ~/intel/vtune_amplifier_xe/bin64/amplxe-cl  -collect general-exploration -- ./tbb_test -s30 -n64 -e fs1
. ~/intel/vtune_amplifier_xe/bin64/amplxe-cl  -collect general-exploration -- ./tbb_test -s30 -n64 -e los
. ~/intel/vtune_amplifier_xe/bin64/amplxe-cl  -collect general-exploration -- ./tbb_test -s30 -n64 -e sor
. ~/intel/vtune_amplifier_xe/bin64/amplxe-cl  -collect general-exploration -- ./tbb_test -s30 -n64 -e mts
. ~/intel/vtune_amplifier_xe/bin64/amplxe-cl  -collect general-exploration -- ./tbb_test -s30 -n64 -e mps
. ~/intel/vtune_amplifier_xe/bin64/amplxe-cl  -collect general-exploration -- ./tbb_test -s30 -n64 -e mss
. ~/intel/vtune_amplifier_xe/bin64/amplxe-cl  -collect general-exploration -- ./tbb_test -s30 -n64 -e s01
. ~/intel/vtune_amplifier_xe/bin64/amplxe-cl  -collect general-exploration -- ./tbb_test -s30 -n64 -e lbk
. ~/intel/vtune_amplifier_xe/bin64/amplxe-cl  -collect general-exploration -- ./tbb_test -s30 -n64 -e bal
echo "Collection success."
