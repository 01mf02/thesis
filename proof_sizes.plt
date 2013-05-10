# i will be set from calling batch.plt; uncomment line below if you want to
# run this plot file without batch.plt
#i = 2

#set terminal pdf
#set output "proof_sizes".i.".pdf"
set terminal tikz size 12cm,6cm
set output "proof_sizes".i.".tex"

# show legend above the plot
set key above

set xlabel "Variables"
set xrange [0:30]
set xtics 5

# different axes for different data sets
if (i == 0) { rules_max =  5000; symbs_max = 150000 }
if (i == 1) { rules_max =  5000; symbs_max =  60000 }
if (i == 2) { rules_max = 25000; symbs_max = 300000 }
if (i == 3) { rules_max =  1000; symbs_max =  10000 }

# filenames
file_b = "sizes_b".i.".dat"
file_d = "sizes_d".i.".dat"

# show numbers like "500k", "5G", ...
set format y "%.0s%c"

set style data linespoints
set style line 1 pi -1 pt 6
set style line 2 pi -1 pt 1

# for debugging, output all line styles
#show style line

set size square 1,0.5
set multiplot layout 1,2

set origin 0,0
set ylabel "Rules"
set yrange [0:rules_max]
plot file_b using 1:2 ls 1 title 'Base', \
	 file_d using 1:2 ls 2 title 'Dec.'

set origin 0.5,0
set ylabel "Symbols"
set yrange [0:symbs_max]
plot file_b using 1:3 ls 1 title 'Base', \
	 file_d using 1:3 ls 2 title 'Dec.'

set nomultiplot


# don't quit terminal immediately after drawing (for X11 output)
#pause -1

set output
set terminal pop
