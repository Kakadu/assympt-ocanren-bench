DataFile1 = ARG1.'/data_points_'.ARG1.'_'.ARG2.'_with_oc.txt'
DataFile2 = ARG1.'/data_points_'.ARG1.'_'.ARG2.'_without_oc.txt'
OutFile =  ARG1.'/plots_'.ARG1.'_'.ARG2.'.ps'
set terminal postscript colour size 8, 6
set output OutFile
plot DataFile1 title "with occurs check", DataFile2 title 'without occurs check'
