#set terminal pdf
#set output "proof_sizes.pdf"
set terminal tikz size 12cm,6cm
set output "proof_sizes.tex"

# show legend above the plot
set key above

set xlabel "Variables"
set xrange [0:30]
set xtics 5

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
set yrange [0:25000]
plot "sizes_b2.dat" using 1:2 ls 1 title 'Base', \
	 "sizes_d2.dat" using 1:2 ls 2 title 'Dec.'
set origin 0.5,0
set ylabel "Symbols"
set yrange [0:300000]
plot "sizes_b2.dat" using 1:3 ls 1 title 'Base', \
	 "sizes_d2.dat" using 1:3 ls 2 title 'Dec.'
set nomultiplot


# don't quit terminal immediately after drawing (for X11 output)
#pause -1

set output
set terminal pop
